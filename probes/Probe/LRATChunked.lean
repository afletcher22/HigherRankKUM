import Mathlib.Tactic.Sat.FromLRAT

/-!
# Kernel-checked LRAT refutations in bounded memory

`lrat_refutation foo cnf lrat` (`Enc.lean`) builds one proof term for the whole LRAT proof, and the
kernel checks it as a single declaration. Its caches grow with the proof: about 26 KB per LRAT
hint, so a 600k-hint certificate needs about 20 GB.

`lrat_refutation_chunked foo cnf lrat budget` does the same checking, split into declarations of at
most about `budget` hints each. After each chunk of steps it adds a theorem `foo.chunk_i`. This
theorem is a balanced conjunction of `ctx.proof c` over the clauses `c` derived so far that later
steps still use. From then on those clauses are proved by projections out of `foo.chunk_i`.
The kernel checks each chunk separately, so its caches are bounded by the chunk.

It adds the same declarations as `lrat_refutation`: `foo.fmla : Sat.Fmla` and
`foo.refute : Sat.Fmla.proof foo.fmla []`.

The proof steps are Mathlib's (`Mathlib.Tactic.Sat.buildProofStep`); only the bookkeeping is new.
-/

namespace Probe.Enc

open Lean Elab Command Term Meta
open Std (HashMap)

/-- A balanced tree of conjunctions, with its type and proof at every node. -/
inductive ATree where
  | leaf (ty pf : Expr)
  | node (ty pf : Expr) (l r : ATree)

def ATree.ty : ATree → Expr
  | .leaf t _ => t
  | .node t _ _ _ => t

def ATree.pf : ATree → Expr
  | .leaf _ p => p
  | .node _ p _ _ => p

/-- The conjunction of `tys[lo:hi]`, proved by `prfs[lo:hi]`. -/
partial def buildATree (tys prfs : Array Expr) (lo hi : Nat) : ATree :=
  if hi ≤ lo + 1 then .leaf tys[lo]! prfs[lo]!
  else
    let mid := (lo + hi) / 2
    let l := buildATree tys prfs lo mid
    let r := buildATree tys prfs mid hi
    .node (mkApp2 (mkConst ``And) l.ty r.ty) (mkApp4 (mkConst ``And.intro) l.ty r.ty l.pf r.pf) l r

/-- For a proof `e` of the tree's conjunction, proofs of its leaves in order. -/
partial def ATree.projs : ATree → Expr → Array Expr → Array Expr
  | .leaf _ _, e, acc => acc.push e
  | .node _ _ l r, e, acc =>
    let acc := l.projs (mkApp3 (mkConst ``And.left) l.ty r.ty e) acc
    r.projs (mkApp3 (mkConst ``And.right) l.ty r.ty e) acc

/-- `lrat_refutation_chunked foo cnf lrat budget` adds `foo.fmla : Sat.Fmla` and
`foo.refute : Sat.Fmla.proof foo.fmla []`, checked in chunks of about `budget` hints. -/
elab "lrat_refutation_chunked " n:ident ppSpace cnf:term:max ppSpace lrat:term:max ppSpace
    budget:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let budget := budget.getNat
  liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    let Std.Internal.Parsec.ParseResult.success _ (_, arr) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if arr.isEmpty then throwError "empty CNF"
    let ctx' := Mathlib.Tactic.Sat.buildConj arr 0 arr.size
    addDecl <| Declaration.defnDecl {
      name := name ++ `fmla, levelParams := [], type := mkConst ``Sat.Fmla, value := ctx'
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
    let ctx := mkConst (name ++ `fmla)
    let Std.Internal.Parsec.ParseResult.success _ steps :=
        Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, lrat.startPos⟩
      | throwError "parse LRAT failed"
    -- the last step that uses each clause
    let mut lastUse : HashMap Nat Nat := {}
    let mut idx := 0
    for step in steps do
      match step with
      | .add _ _ pf => for i in pf do lastUse := lastUse.insert i.natAbs idx
      | .del _ => pure ()
      idx := idx + 1
    let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
    let mut db := (Mathlib.Tactic.Sat.buildClauses arr ctx 0 arr.size ctx' p default).2
    let mut derived : Array Nat := #[]
    let mut used := 0
    let mut chunk := 0
    idx := 0
    for step in steps do
      match step with
      | .del ds => db := ds.foldl (·.erase ·) db
      | .add i ns pf =>
        let e := Mathlib.Tactic.Sat.buildClause ns
        match Mathlib.Tactic.Sat.buildProofStep db ns pf ctx e with
        | .error msg => throwError msg
        | .ok proof =>
          if ns.isEmpty then
            addDecl <| Declaration.thmDecl {
              name := name ++ `refute, levelParams := []
              type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx (mkConst ``Sat.Clause.nil)
              value := proof }
            return
          db := db.insert i { lits := ns, expr := e, proof }
          derived := derived.push i
          used := used + pf.size
          if used ≥ budget then
            -- export the derived clauses that later steps still use
            let mut live : Array (Nat × Mathlib.Tactic.Sat.Clause) := #[]
            for j in derived do
              if lastUse.getD j 0 > idx then
                if let some cl := db[j]? then live := live.push (j, cl)
            if !live.isEmpty then
              let tys := live.map fun (_, cl) => mkApp2 (mkConst ``Sat.Fmla.proof) ctx cl.expr
              let prfs := live.map fun (_, cl) => cl.proof
              let tree := buildATree tys prfs 0 live.size
              chunk := chunk + 1
              let cname := name ++ Name.mkSimple s!"chunk_{chunk}"
              addDecl <| Declaration.thmDecl {
                name := cname, levelParams := [], type := tree.ty, value := tree.pf }
              let projs := tree.projs (mkConst cname) #[]
              let mut k := 0
              for (j, cl) in live do
                db := db.insert j { cl with proof := projs[k]! }
                k := k + 1
            derived := #[]
            used := 0
      idx := idx + 1
    throwError "no empty clause"

end Probe.Enc
