"""Move the kernel-checked rank-4 proof from branch ``probe/rank4`` into the main tree.

Usage
-----
    python scripts/migrate_probe.py PROBE_TREE MAIN_TREE [--dry-run] [--force] [--root-imports]

``PROBE_TREE``
    A checkout of branch ``probe/rank4`` (it has ``probes/Probe/`` and ``probes/data/``).
    It is only read, never modified.
``MAIN_TREE``
    The checkout that receives the proof (``main`` or the research branch). It must already
    contain every ``HigherRankKUM.*`` module that the probe modules import.
``--dry-run``
    Print the plan and run every check, but write nothing.
``--force``
    Overwrite destination files that already exist (by default the script stops).
``--root-imports``
    Also add the new main-library modules to ``HigherRankKUM.lean``, so that the default
    target builds them. Off by default: SerialExchange, LemmaH, LemmaU and XP.Insert are heavy,
    and the main CI builds an explicit module list.

What moves where
----------------
The proof is the import closure of ``Probe.Rank4.Final`` (theorem
``HigherRankKUM.solvesKUMAtRank_four``). It is split in three parts.

* SAT encoding layer: ``probes/Probe/<M>.lean`` goes to ``HigherRankKUM/SAT/<M>.lean``
  (module ``HigherRankKUM.SAT.<M>``). These are the encodings, the soundness and bridge lemmas,
  the chunked LRAT checker and the ``f_certificate`` / ``h_certificate`` commands. They hold
  no certificate data.
* Rank-4 paper lemmas (human proofs, no certificates):
  ``probes/Probe/Rank4/<M>.lean`` goes to ``HigherRankKUM/Rank4/<M>.lean``, and
  ``probes/Probe/XP/<M>.lean`` goes to ``HigherRankKUM/Rank4/XP/<M>.lean``. The XP modules keep
  their namespace ``HigherRankKUM.XP``. ``TheoremDCert`` is here too: since XP it has no
  certificate inputs (Theorem D with Kotlar-Ziv for n = 8 and pair-chain insertion).
* Certificates and assembly: the certificate modules ``Chain10``, ``Hit14G`` and ``Hit14Line``,
  ``Rank4/Kum10Chain`` (it imports ``Chain10``), ``Rank4/Full`` and ``Rank4/Final`` go to
  ``HigherRankKUMCert/<M>.lean`` (library ``HigherRankKUMCert``, not a default target). The
  data files they read with ``include_str`` go to ``HigherRankKUMCert/data/``, and the
  ``include_str`` paths are rewritten. The script adds a ``[[lean_lib]]`` entry for
  ``HigherRankKUMCert`` to ``lakefile.toml`` and a root file ``HigherRankKUMCert.lean`` that
  imports ``HigherRankKUMCert.Final``.

Rewrites in every moved file: ``import Probe.*`` lines use the new module names; the namespace
``Probe.Enc`` becomes ``HigherRankKUM.SAT``, also inside longer names (the certificate
namespaces such as ``Probe.Enc.Chain10``, and the quoted names such as ``Probe.Enc.WF.order``
that the certificate commands pass to ``mkConst``); module names in comments are updated.

Checks (the script stops before writing if one fails)
-----------------------------------------------------
* The module tables below equal the import closure of ``Probe.Rank4.Final`` in PROBE_TREE.
* No main-library module imports a ``HigherRankKUMCert`` module.
* No main-library module reads data with ``include_str``.
* Every non-probe ``HigherRankKUM.*`` import exists in MAIN_TREE.
* No ``Probe`` name is left after the rewrite.
* No destination file exists already (unless ``--force``).

After running
-------------
Compile only on GitHub Actions. Build the heavy modules one at a time first (memory):
``HigherRankKUM.Rank4.SerialExchange``, ``HigherRankKUM.Rank4.Kum8``,
``HigherRankKUM.Rank4.XP.Insert``, ``HigherRankKUMCert.Chain10``, ``HigherRankKUMCert.Hit14G``,
``HigherRankKUMCert.Hit14Line``, ``HigherRankKUM.Rank4.LemmaH``, ``HigherRankKUM.Rank4.LemmaU``.
Then build and replay (leanchecker) ``HigherRankKUMCert.Final``. The expected axioms of
``solvesKUMAtRank_four`` are ``[propext, Classical.choice, Quot.sound]``.

The namespace change can in principle change name resolution inside the SAT modules (the
innermost namespace wins, and ``HigherRankKUM`` is now an enclosing namespace instead of an
opened one), so the CI build is the real test of the migration.
"""
import argparse
import os
import re
import shutil
import sys

# --- module tables (probe module suffix -> new module name) ---------------------------------

# SAT encoding layer -> HigherRankKUM/SAT/
SAT = ["Enc", "EncSound", "EncBridge", "ExtEnc", "ExtBridge", "EncF", "EncFBridge", "EncH",
       "EncHBridge", "EncHBridgeG", "LRATChunked", "Cert", "Kum10Data"]
# rank-4 paper lemmas -> HigherRankKUM/Rank4/
RANK4 = ["TheoremD", "Hitting", "LemmaH", "LemmaUBasic", "LemmaU", "SerialExchange", "Kum8",
         "HitGeFour", "TheoremDCert"]
# pair-chain insertion (XP) -> HigherRankKUM/Rank4/XP/
XP = ["Basic", "Main", "Local", "Chain", "Insert"]
# certificates and assembly -> HigherRankKUMCert/ (not a default target)
CERT = {
    "Chain10": "Chain10", "Hit14G": "Hit14G", "Hit14Line": "Hit14Line",
    "Rank4.Kum10Chain": "Kum10Chain", "Rank4.Full": "Full", "Rank4.Final": "Final",
}

ROOT = "Probe.Rank4.Final"
CERT_LIB = "HigherRankKUMCert"
MAIN_LIB = "HigherRankKUM"

MODMAP = {}
for _m in SAT:
    MODMAP[f"Probe.{_m}"] = f"{MAIN_LIB}.SAT.{_m}"
for _m in RANK4:
    MODMAP[f"Probe.Rank4.{_m}"] = f"{MAIN_LIB}.Rank4.{_m}"
for _m in XP:
    MODMAP[f"Probe.XP.{_m}"] = f"{MAIN_LIB}.Rank4.XP.{_m}"
for _m, _n in CERT.items():
    MODMAP[f"Probe.{_m}"] = f"{CERT_LIB}.{_n}"

IMPORT_RE = re.compile(r"^(\s*import\s+)(\S+)", re.M)
INCLUDE_RE = re.compile(r'include_str\s+"([^"]+)"')
NAMESPACE_RE = re.compile(r"\bProbe\.Enc\b")
MODULE_MENTION_RE = re.compile(r"\bProbe(?:\.[A-Za-z0-9_]+)+")
LEFTOVER_RE = re.compile(r"\bProbe\b")

CERT_LAKEFILE_ENTRY = f"""
# SAT certificates and the rank-4 assembly (not part of the default target)
[[lean_lib]]
name = "{CERT_LIB}"
"""


def fail(msg):
    sys.exit("error: " + msg)


def module_path(tree, mod, prefix=()):
    return os.path.join(tree, *prefix, *mod.split(".")) + ".lean"


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def write(path, text):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def import_closure(probe):
    seen, stack = set(), [ROOT]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        p = module_path(probe, m, ("probes",))
        if not os.path.isfile(p):
            fail(f"{m} is imported but {p} does not exist")
        seen.add(m)
        stack += [i for _, i in IMPORT_RE.findall(read(p)) if i.startswith("Probe.")]
    return seen


def rewrite(text, src_dir, dst_dir, data_dir, data_plan):
    """Rewrite one module moved from ``src_dir`` to ``dst_dir``.

    Data files it reads are recorded in ``data_plan`` (source path -> path in ``data_dir``).
    """
    def imp(mo):
        m = mo.group(2)
        if m.startswith("Probe."):
            if m not in MODMAP:
                fail(f"unmapped import {m}")
            m = MODMAP[m]
        return mo.group(1) + m
    text = IMPORT_RE.sub(imp, text)

    def inc(mo):
        src = os.path.normpath(os.path.join(src_dir, mo.group(1)))
        dst = os.path.join(data_dir, os.path.basename(src))
        data_plan[src] = dst
        return 'include_str "' + os.path.relpath(dst, dst_dir).replace(os.sep, "/") + '"'
    text = INCLUDE_RE.sub(inc, text)

    text = NAMESPACE_RE.sub(f"{MAIN_LIB}.SAT", text)

    def mention(mo):
        m = mo.group(0)
        return MODMAP.get(m, m)
    return MODULE_MENTION_RE.sub(mention, text)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("probe_tree")
    ap.add_argument("main_tree")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--root-imports", action="store_true")
    args = ap.parse_args()
    probe, main_tree = args.probe_tree, args.main_tree
    data_dst_dir = os.path.join(main_tree, CERT_LIB, "data")

    # 1. the tables must match the proof on the probe branch
    closure = import_closure(probe)
    missing = sorted(closure - set(MODMAP))
    extra = sorted(set(MODMAP) - closure)
    if missing or extra:
        fail(f"module tables out of date: not mapped {missing}, not in the closure {extra}")
    all_probe = set()
    for dirpath, _, files in os.walk(os.path.join(probe, "probes", "Probe")):
        for fn in files:
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), os.path.join(probe, "probes"))
                all_probe.add(rel[:-5].replace(os.sep, "."))
    for m in sorted(all_probe - closure):
        print(f"note: {m} is not used by {ROOT}; not moved")

    # 2. rewrite in memory and check
    outputs, data_plan, problems = {}, {}, []
    for old, new in sorted(MODMAP.items()):
        src = module_path(probe, old, ("probes",))
        dst = module_path(main_tree, new)
        plan = {}
        text = rewrite(read(src), os.path.dirname(src), os.path.dirname(dst), data_dst_dir, plan)
        is_main = not new.startswith(CERT_LIB + ".")
        imports = [i for _, i in IMPORT_RE.findall(text)]
        if is_main:
            bad = [i for i in imports if i.startswith(CERT_LIB + ".")]
            if bad:
                problems.append(f"{new} (main library) imports certificate modules {bad}")
            if plan:
                problems.append(f"{new} (main library) reads data files {sorted(plan)}")
        for i in imports:
            if (i.startswith(MAIN_LIB + ".") and i not in MODMAP.values()
                    and not os.path.isfile(module_path(main_tree, i))):
                problems.append(f"{new} imports {i}, which is missing from {main_tree}")
        for n, line in enumerate(text.splitlines(), 1):
            if LEFTOVER_RE.search(line):
                problems.append(f"{new}:{n}: Probe name left after rewrite: {line.strip()}")
        data_plan.update(plan)
        outputs[dst] = (old, new, text)
    for src in data_plan:
        if not os.path.isfile(src):
            problems.append(f"data file {src} does not exist")
    if problems:
        fail("\n  ".join(["checks failed:"] + problems))

    root_file = os.path.join(main_tree, CERT_LIB + ".lean")
    root_text = f"import {CERT_LIB}.Final\n"
    targets = list(outputs) + list(data_plan.values()) + [root_file]
    existing = [t for t in targets if os.path.exists(t)]
    if existing and not args.force:
        fail("destination files exist (use --force to overwrite):\n  " + "\n  ".join(existing))

    lakefile = os.path.join(main_tree, "lakefile.toml")
    lake_text = read(lakefile)
    add_lake = f'name = "{CERT_LIB}"' not in lake_text

    root_imports = []
    main_root = os.path.join(main_tree, MAIN_LIB + ".lean")
    if args.root_imports:
        have = set(i for _, i in IMPORT_RE.findall(read(main_root)))
        root_imports = [n for _, n, _ in sorted(outputs.values(), key=lambda v: v[1])
                        if not n.startswith(CERT_LIB + ".") and n not in have]

    # 3. report the plan
    for dst, (old, new, _) in sorted(outputs.items(), key=lambda kv: kv[1][1]):
        print(f"{old} -> {new}")
    for src, dst in sorted(data_plan.items()):
        print(f"data {os.path.relpath(src, probe)} -> {os.path.relpath(dst, main_tree)}")
    print(f"root file {CERT_LIB}.lean: {root_text.strip()}")
    print(f"lakefile.toml: {'add' if add_lake else 'already has'} lean_lib {CERT_LIB}")
    if args.root_imports:
        print(f"{MAIN_LIB}.lean: add {len(root_imports)} imports")
    print(f"{len(outputs)} modules, {len(data_plan)} data files")
    if args.dry_run:
        print("dry run: nothing written")
        return

    # 4. write
    for dst, (_, _, text) in outputs.items():
        write(dst, text)
    for src, dst in data_plan.items():
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(src, dst)
    write(root_file, root_text)
    if add_lake:
        write(lakefile, lake_text.rstrip("\n") + "\n" + CERT_LAKEFILE_ENTRY)
    if root_imports:
        lines = read(main_root).splitlines(keepends=True)
        last = max(i for i, line in enumerate(lines) if IMPORT_RE.match(line))
        if not lines[last].endswith("\n"):
            lines[last] += "\n"
        lines[last + 1:last + 1] = [f"import {n}\n" for n in root_imports]
        write(main_root, "".join(lines))
    print("done")


if __name__ == "__main__":
    main()
