import Probe.LRATChunked
import Probe.EncF
import Probe.EncH

/-!
# Certificates in bounded memory

A certificate is a core CNF, an LRAT refutation of it, and one witness per clause. The checks are
that every witness is valid and that the witnesses regenerate the CNF exactly. Run as single
kernel evaluations, these checks and the LRAT refutation each hold memory proportional to the whole
certificate: about 0.6 MB per clause for the formula comparison.

`f_certificate foo cnf lrat wit valid gen budget slice` (and `h_certificate` for the hitting
claims) splits everything into bounded declarations:

* `foo.fmla` is a balanced `Sat.Fmla.and` tree over slices `foo.fmla_i` of `slice` clauses each.
  `foo.ws` is the matching `List.append` tree over the witness slices `foo.ws_i`.
* `foo.refute : Sat.Fmla.proof foo.fmla []` is checked in LRAT chunks of about `budget` hints, as
  in `lrat_refutation_chunked`.
* For each slice, `foo.valid_i` (every witness is valid) and `foo.eq_i` (the witnesses regenerate
  the slice) are proved by kernel evaluation.
* `foo.ws_valid : foo.ws.all valid = true` and
  `foo.fmla_eq : (foo.fmla : List (List Sat.Literal)) = foo.ws.map gen` combine the slices along
  the tree.
-/

namespace Probe.Enc

open Lean Elab Command Term Meta
open Std (HashMap)

theorem all_append_true {β : Type} {f : β → Bool} {a b : List β} (ha : a.all f = true)
    (hb : b.all f = true) : (a ++ b).all f = true := by
  simp [List.all_append, ha, hb]

theorem fmla_and_map {β : Type} {g : β → List Sat.Literal} {a b : Sat.Fmla} {as bs : List β}
    (ha : (a : List (List Sat.Literal)) = as.map g)
    (hb : (b : List (List Sat.Literal)) = bs.map g) :
    (Sat.Fmla.and a b : List (List Sat.Literal)) = (as ++ bs).map g :=
  (congrArg₂ (· ++ ·) ha hb).trans (List.map_append ..).symm

/-- A balanced tree over `xs[lo:hi]`, built with a binary node. -/
partial def balancedTree (node : Expr → Expr → Expr) (xs : Array Expr) (lo hi : Nat) : Expr :=
  if hi ≤ lo + 1 then xs[lo]!
  else
    let mid := (lo + hi) / 2
    node (balancedTree node xs lo mid) (balancedTree node xs mid hi)

/-- The same tree shape, combining proofs. -/
partial def balancedProof (combine : Expr → Expr → MetaM Expr) (xs : Array Expr) (lo hi : Nat) :
    MetaM Expr := do
  if hi ≤ lo + 1 then return xs[lo]!
  else
    let mid := (lo + hi) / 2
    combine (← balancedProof combine xs lo mid) (← balancedProof combine xs mid hi)

/-- Proofs of `ctx.subsumes fᵢ` for the leaves of the tree `f` over `xs[lo:hi]`, given
`p : ctx.subsumes f`. -/
partial def leafSubsumes (ctx : Expr) (lo hi : Nat) (f p : Expr) (acc : Array Expr) :
    Array Expr :=
  if hi ≤ lo + 1 then acc.push p
  else
    let mid := (lo + hi) / 2
    let f₁ := f.appFn!.appArg!
    let f₂ := f.appArg!
    let p₁ := mkApp4 (Lean.mkConst ``Sat.Fmla.subsumes_left) ctx f₁ f₂ p
    let p₂ := mkApp4 (Lean.mkConst ``Sat.Fmla.subsumes_right) ctx f₁ f₂ p
    leafSubsumes ctx mid hi f₂ p₂ (leafSubsumes ctx lo mid f₁ p₁ acc)

def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

def addDefn (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.defnDecl {
    name, levelParams := [], type, value
    hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }

/-- The whole construction; `ws` are the witness expressions, of type `wty`. -/
def mkCertificate (name : Name) (cnf lrat : String) (ws : Array Expr) (wty validFn genFn : Expr)
    (budget slice : Nat) : TermElabM Unit := do
  let Std.Internal.Parsec.ParseResult.success _ (_, arr) :=
      Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  if arr.size != ws.size then
    throwError "{arr.size} clauses but {ws.size} witnesses"
  let fmlaTy := Lean.mkConst ``Sat.Fmla
  let wsTy := mkApp (Lean.mkConst ``List [Level.zero]) wty
  -- slices
  let nslices := (arr.size + slice - 1) / slice
  let mut fConsts : Array Expr := #[]
  let mut fVals : Array Expr := #[]
  let mut wConsts : Array Expr := #[]
  for i in [0:nslices] do
    let lo := i * slice
    let hi := min arr.size (lo + slice)
    let fv := Mathlib.Tactic.Sat.buildConj arr lo hi
    let fn := name ++ Name.mkSimple s!"fmla_{i}"
    addDefn fn fmlaTy fv
    fConsts := fConsts.push (Lean.mkConst fn)
    fVals := fVals.push fv
    let wn := name ++ Name.mkSimple s!"ws_{i}"
    addDefn wn wsTy (balancedList wty ws lo hi)
    wConsts := wConsts.push (Lean.mkConst wn)
  let andNode := fun a b => mkApp2 (Lean.mkConst ``Sat.Fmla.and) a b
  let top := balancedTree andNode fConsts 0 nslices
  addDefn (name ++ `fmla) fmlaTy top
  let ctx := Lean.mkConst (name ++ `fmla)
  let appNode := fun a b => mkApp3 (Lean.mkConst ``List.append [Level.zero]) wty a b
  addDefn (name ++ `ws) wsTy (balancedTree appNode wConsts 0 nslices)
  -- the original clauses, slice by slice
  let p := mkApp (Lean.mkConst ``Sat.Fmla.subsumes_self) ctx
  let sliceProofs := leafSubsumes ctx 0 nslices top p #[]
  let mut accum : Nat × HashMap Nat Mathlib.Tactic.Sat.Clause := (0, {})
  for i in [0:nslices] do
    let lo := i * slice
    let hi := min arr.size (lo + slice)
    accum := Mathlib.Tactic.Sat.buildClauses arr ctx lo hi fVals[i]! sliceProofs[i]! accum
  let mut db := accum.2
  -- the LRAT proof, in chunks
  let Std.Internal.Parsec.ParseResult.success _ steps :=
      Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, lrat.startPos⟩
    | throwError "parse LRAT failed"
  let mut lastUse : HashMap Nat Nat := {}
  let mut idx := 0
  for step in steps do
    match step with
    | .add _ _ pf => for j in pf do lastUse := lastUse.insert j.natAbs idx
    | .del _ => pure ()
    idx := idx + 1
  let mut derived : Array Nat := #[]
  let mut used := 0
  let mut chunk := 0
  let mut done := false
  idx := 0
  for step in steps do
    if done then break
    match step with
    | .del ds => db := ds.foldl (·.erase ·) db
    | .add i ns pf =>
      let e := Mathlib.Tactic.Sat.buildClause ns
      match Mathlib.Tactic.Sat.buildProofStep db ns pf ctx e with
      | .error msg => throwError msg
      | .ok proof =>
        if ns.isEmpty then
          addThm (name ++ `refute)
            (mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx (Lean.mkConst ``Sat.Clause.nil)) proof
          done := true
        else
          db := db.insert i { lits := ns, expr := e, proof }
          derived := derived.push i
          used := used + pf.size
          if used ≥ budget then
            let mut live : Array (Nat × Mathlib.Tactic.Sat.Clause) := #[]
            for j in derived do
              if lastUse.getD j 0 > idx then
                if let some cl := db[j]? then live := live.push (j, cl)
            if !live.isEmpty then
              let tys := live.map fun (_, cl) =>
                mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx cl.expr
              let prfs := live.map fun (_, cl) => cl.proof
              let tree := buildATree tys prfs 0 live.size
              chunk := chunk + 1
              let cname := name ++ Name.mkSimple s!"chunk_{chunk}"
              addThm cname tree.ty tree.pf
              let projs := tree.projs (Lean.mkConst cname) #[]
              let mut k := 0
              for (j, cl) in live do
                db := db.insert j { cl with proof := projs[k]! }
                k := k + 1
            derived := #[]
            used := 0
    idx := idx + 1
  if !done then throwError "no empty clause"
  -- the slice checks, by kernel evaluation
  let trueE := Lean.mkConst ``Bool.true
  let reflTrue := mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) (Lean.mkConst ``Bool) trueE
  let mut validPfs : Array Expr := #[]
  let mut eqPfs : Array Expr := #[]
  for i in [0:nslices] do
    let allE ← mkAppM ``List.all #[wConsts[i]!, validFn]
    let vn := name ++ Name.mkSimple s!"valid_{i}"
    addThm vn (← mkEq allE trueE) reflTrue
    validPfs := validPfs.push (Lean.mkConst vn)
    let mapE ← mkAppM ``List.map #[genFn, wConsts[i]!]
    let beqE := mkApp2 (Lean.mkConst ``Probe.Enc.fmlaBEq) fConsts[i]! mapE
    let en := name ++ Name.mkSimple s!"eq_{i}"
    addThm en (← mkEq beqE trueE) reflTrue
    eqPfs := eqPfs.push (← mkAppM ``Probe.Enc.fmlaBEq_eq #[Lean.mkConst en])
  -- combined along the tree
  let wsC := Lean.mkConst (name ++ `ws)
  let allWs ← mkAppM ``List.all #[wsC, validFn]
  let vpf ← balancedProof (fun a b => mkAppM ``Probe.Enc.all_append_true #[a, b]) validPfs 0
    nslices
  addThm (name ++ `ws_valid) (← mkEq allWs trueE) vpf
  let listListLit := mkApp (Lean.mkConst ``List [Level.zero])
    (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sat.Literal))
  let mapWs ← mkAppM ``List.map #[genFn, wsC]
  let epf ← balancedProof (fun a b => mkAppM ``Probe.Enc.fmla_and_map #[a, b]) eqPfs 0 nslices
  addThm (name ++ `fmla_eq)
    (mkApp3 (Lean.mkConst ``Eq [Level.one]) listListLit ctx mapWs) epf

/-- Parse `lean_witness_f.py` witness lines. -/
def parseWF (text : String) : MetaM (Array Expr) := do
  let nat := fun (k : Nat) => mkRawNatLit k
  let mut ws : Array Expr := #[]
  for line in text.splitOn "\n" do
    match (line.splitOn " ").filter (· ≠ "") with
    | [] => pure ()
    | k :: rest =>
      let a := rest.map String.toNat!
      let e ← match k, a with
        | "o", [X, v] => pure <| mkApp2 (Lean.mkConst ``Probe.Enc.WF.order) (nat X) (nat v)
        | "c", [X, v] => pure <| mkApp2 (Lean.mkConst ``Probe.Enc.WF.cap) (nat X) (nat v)
        | "l", [X, v] => pure <| mkApp2 (Lean.mkConst ``Probe.Enc.WF.low) (nat X) (nat v)
        | "m", [X, x, v] =>
          pure <| mkApp3 (Lean.mkConst ``Probe.Enc.WF.mono) (nat X) (nat x) (nat v)
        | "i", [X, x, v] =>
          pure <| mkApp3 (Lean.mkConst ``Probe.Enc.WF.inc) (nat X) (nat x) (nat v)
        | "s", [X, x, y, v] =>
          pure <| mkApp4 (Lean.mkConst ``Probe.Enc.WF.sub) (nat X) (nat x) (nat y) (nat v)
        | "f", [X, v, b] =>
          pure <| mkApp3 (Lean.mkConst ``Probe.Enc.WF.fact) (nat X) (nat v) (toExpr (b == 1))
        | "w", s => pure <| mkApp (Lean.mkConst ``Probe.Enc.WF.win) (toExpr s)
        | _, _ => throwError "bad witness line: {line}"
      ws := ws.push e
  return ws

/-- Parse `lean_witness_h.py` witness lines. -/
def parseWH (text : String) : MetaM (Array Expr) := do
  let nat := fun (k : Nat) => mkRawNatLit k
  let mut ws : Array Expr := #[]
  for line in text.splitOn "\n" do
    match (line.splitOn " ").filter (· ≠ "") with
    | [] => pure ()
    | k :: rest =>
      let a := rest.map String.toNat!
      let e ← match k, a with
        | "o", [X, v] => pure <| mkApp2 (Lean.mkConst ``Probe.Enc.WH.order) (nat X) (nat v)
        | "c", [X, v] => pure <| mkApp2 (Lean.mkConst ``Probe.Enc.WH.cap) (nat X) (nat v)
        | "l", [X, v] => pure <| mkApp2 (Lean.mkConst ``Probe.Enc.WH.low) (nat X) (nat v)
        | "m", [X, x, v] =>
          pure <| mkApp3 (Lean.mkConst ``Probe.Enc.WH.mono) (nat X) (nat x) (nat v)
        | "i", [X, x, v] =>
          pure <| mkApp3 (Lean.mkConst ``Probe.Enc.WH.inc) (nat X) (nat x) (nat v)
        | "s", [X, x, y, v] =>
          pure <| mkApp4 (Lean.mkConst ``Probe.Enc.WH.sub) (nat X) (nat x) (nat y) (nat v)
        | "f", [X, v, b] =>
          pure <| mkApp3 (Lean.mkConst ``Probe.Enc.WH.fact) (nat X) (nat v) (toExpr (b == 1))
        | "h", [B] => pure <| mkApp (Lean.mkConst ``Probe.Enc.WH.hit) (nat B)
        | _, _ => throwError "bad witness line: {line}"
      ws := ws.push e
  return ws

def elabFn (stx : Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- `f_certificate foo cnf lrat wit valid gen budget slice`: a certificate with `WF` witnesses. -/
elab "f_certificate " n:ident ppSpace cnf:term:max ppSpace lrat:term:max ppSpace wit:term:max
    ppSpace valid:term:max ppSpace gen:term:max ppSpace budget:num ppSpace slice:num :
    command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (Lean.mkConst ``String) lrat
    let wit ← unsafe evalTerm String (Lean.mkConst ``String) wit
    let ws ← parseWF wit
    mkCertificate name cnf lrat ws (Lean.mkConst ``Probe.Enc.WF) (← elabFn valid)
      (← elabFn gen) budget.getNat slice.getNat

/-- `h_certificate foo cnf lrat wit valid gen budget slice`: a certificate with `WH` witnesses. -/
elab "h_certificate " n:ident ppSpace cnf:term:max ppSpace lrat:term:max ppSpace wit:term:max
    ppSpace valid:term:max ppSpace gen:term:max ppSpace budget:num ppSpace slice:num :
    command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (Lean.mkConst ``String) lrat
    let wit ← unsafe evalTerm String (Lean.mkConst ``String) wit
    let ws ← parseWH wit
    mkCertificate name cnf lrat ws (Lean.mkConst ``Probe.Enc.WH) (← elabFn valid)
      (← elabFn gen) budget.getNat slice.getNat

end Probe.Enc
