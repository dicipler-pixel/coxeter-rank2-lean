#!/usr/bin/env python3
# SCRIPT: COXETER-RANK2-LEAN-VERIFY-01
"""Audit the Lean library after `lake build`.

Why each check proves what it claims:

1. Axiom audit. `lake build` accepts a proof that uses `sorry` with only a
   warning, and a declared `axiom` would be accepted silently. `#print axioms`
   asks the kernel which axioms each theorem actually rests on. Requiring the
   answer to lie inside {propext, Classical.choice, Quot.sound} (the standard
   three every Mathlib theorem may use) rules out `sorry` (sorryAx), project
   axioms, and native_decide (Lean.ofReduceBool) for every named theorem.

2. Theorem inventory. The script discovers theorem names from the source files
   and fails if any expected module is missing or the count drops, so a theorem
   cannot silently disappear from the audit.

3. False controls. Each file in FalseControls/ states something deliberately
   false. It must FAIL to compile, and it must fail for a mathematical reason
   (unsolved goals, a failed tactic, a proposition proved false), not because of
   a typo or a missing name. This shows the checker can say no: a pipeline that
   accepts everything would pass the first two checks and fail this one.

4. Hashes. The SHA-256 of every source file is written to the report, so anyone
   can confirm the checked files are the files in the repository.
"""
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CONFIG = json.loads((pathlib.Path(__file__).resolve().parent / "config.json").read_text())
MODULES = [(m["module"], m["path"]) for m in CONFIG["modules"]]
EXPECTED_THEOREMS = CONFIG["expected_theorems"]
EXPECTED_FALSE_CONTROLS = CONFIG["expected_false_controls"]
ROOT_IMPORTS = CONFIG["root_imports"]
# Private helper lemmas cannot be named from another file, so they are not listed; their
# axioms are audited through every public theorem that uses them.
THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+)?theorem\s+([^\s:({\[]+)", re.M)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.M)
MATH_FAILURE = re.compile(
    r"unsolved goals|proved that the proposition.*false|tactic '.*' failed|"
    r"linarith failed|failed to prove|decide failed|norm_num failed|type mismatch|"
    r"made no progress|failed to simplify",
    re.S | re.I)
INFRA_FAILURE = re.compile(
    r"unknown (?:module|identifier|constant|namespace)|unexpected token|"
    r"object file .* does not exist|invalid field", re.I)


LAST_OUTPUT = ""


def run(argv: list[str]) -> subprocess.CompletedProcess:
    global LAST_OUTPUT
    proc = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    LAST_OUTPUT = " ".join(argv) + "\n" + proc.stdout + proc.stderr
    return proc


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def theorems_in(path: pathlib.Path) -> list[str]:
    text = strip_comments(path.read_text())
    spaces = sorted(set(NAMESPACE_RE.findall(text)))
    if len(spaces) != 1:
        raise SystemExit(f"{path}: expected exactly one namespace, found {spaces}")
    return [f"{spaces[0]}.{name}" for name in THEOREM_RE.findall(text)]


LAKEFILE = ROOT / "lakefile.toml"
DEFINITION_MODULES = set(CONFIG.get("definition_modules", []))


def lake_roots() -> list[str]:
    """The modules Lake actually builds, read from the lakefile."""
    text = LAKEFILE.read_text() if LAKEFILE.exists() else ""
    found = re.findall(r"roots\s*=\s*\[([^\]]*)\]", text, re.S)
    return re.findall(r'"([^"]+)"', found[0]) if found else []


def check_every_built_module_is_accounted_for() -> None:
    """A module that Lake builds but this file never audits is a silent gap.

    Every root must either be in the theorem inventory (and so be counted, hashed and
    axiom-audited) or be named in `definition_modules` as carrying no theorems. Adding a
    Lean file and forgetting the inventory then fails here rather than passing quietly.
    """
    listed = {module for module, _ in MODULES} | DEFINITION_MODULES
    missing = [name for name in lake_roots() if name not in listed]
    if missing:
        raise SystemExit(
            f"lakefile builds {missing}, which is neither in `modules` nor in "
            f"`definition_modules` of scripts/config.json: it would be built and never audited")


SUBMISSIONS = ROOT / "swarm" / "submissions"
MANIFEST = SUBMISSIONS / "MANIFEST.tsv"


def read_manifest() -> list[tuple[str, str, str]]:
    """(file, status, claim) for each row of the submission manifest.

    CI gates what is *claimed*, not every file that happens to be in the directory. A route that
    was accepted once and is documented here stays gated; a duplicate kept for the record is marked
    archived. Either way the file is named, so nothing drops out of the account silently.
    """
    if not MANIFEST.exists():
        raise SystemExit(f"missing {MANIFEST.relative_to(ROOT)}: the recorded submissions are not "
                         f"manifested, so CI cannot know which ones back a published claim")
    rows: list[tuple[str, str, str]] = []
    for line in MANIFEST.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            raise SystemExit(f"malformed manifest row: {line!r}")
        fname, status = parts[0].strip(), parts[1].strip()
        claim = parts[2].strip() if len(parts) > 2 else ""
        if status not in ("gate", "archived"):
            raise SystemExit(f"manifest row {fname}: unknown status {status!r}")
        rows.append((fname, status, claim))
    return rows


def check_recorded_submissions() -> dict[str, str]:
    """Gate the manifested claims under the same toolchain as the library.

    `swarm/RESULT.md` claims that several statements were proved by independent routes. The files
    backing those claims are written and gated in a development VM whose Lean is not the pinned
    one, so each manifested claim is put through `scripts/gate.py` here, with this process's
    LEAN_PATH, which in CI is the pinned Mathlib. Archived rows are not re-gated; they were gated
    when accepted and exist as the historical record.
    """
    if not SUBMISSIONS.is_dir():
        return {}
    rows = read_manifest()
    on_disk = {p.name for p in SUBMISSIONS.glob("*.lean")}
    listed = {f for f, _, _ in rows}
    missing = sorted(listed - on_disk)
    if missing:
        raise SystemExit(f"manifest names files that do not exist: {missing}")
    unaccounted = sorted(on_disk - listed)
    if unaccounted:
        raise SystemExit(
            f"submissions not in {MANIFEST.name}: {unaccounted}. Every recorded file must be listed "
            f"as `gate` (it backs a claim) or `archived` (kept for the record).")
    base = os.environ.get("LEAN_PATH", "")
    if not base:
        base = run(["lake", "env", "printenv", "LEAN_PATH"]).stdout.strip()
    env = dict(os.environ)
    env["LEAN_PATH"] = base
    results: dict[str, str] = {}
    for fname, status, _claim in rows:
        if status != "gate":
            results[fname] = "archived"
            continue
        path = SUBMISSIONS / fname
        proc = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "gate.py"),
             "--submission", str(path), "--partial"],
            cwd=ROOT, env=env, capture_output=True, text=True)
        results[fname] = "pass" if proc.returncode == 0 else "FAIL"
        if proc.returncode != 0:
            raise SystemExit(f"claimed submission failed the gate: {fname}\n"
                             f"{proc.stdout[-3000:]}{proc.stderr[-2000:]}")
    return results


def main() -> int:
    OUT.mkdir(exist_ok=True)
    check_every_built_module_is_accounted_for()
    report: dict = {"lean": run(["lean", "--version"]).stdout.strip(), "modules": {},
                   "lake_roots": lake_roots(), "definition_modules": sorted(DEFINITION_MODULES)}

    # Inventory and hashes.
    names: list[str] = []
    for module, rel in MODULES:
        path = ROOT / rel
        found = theorems_in(path)
        if not found:
            raise SystemExit(f"no theorems found in {module}")
        report["modules"][module] = {
            "file": rel,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "theorems": len(found),
        }
        names += found
    total = sum(v["theorems"] for v in report["modules"].values())
    if total != EXPECTED_THEOREMS:
        raise SystemExit(f"inventory changed: {total} theorems, expected {EXPECTED_THEOREMS}")
    report["theorems"] = total

    # Axiom audit.
    audit = OUT / "AxiomAudit.lean"
    lines = [f"import {m}" for m in ROOT_IMPORTS] + [""]
    lines += [f"#print axioms {name}" for name in names]
    audit.write_text("\n".join(lines) + "\n")
    proc = run(["lake", "env", "lean", str(audit.relative_to(ROOT))])
    log = proc.stdout + proc.stderr
    (OUT / "axioms.log").write_text(log)
    if proc.returncode != 0:
        print(log)
        raise SystemExit("axiom audit file did not compile")
    axioms: dict[str, list[str]] = {}
    for name in names:
        dep = re.search(re.escape(f"'{name}' depends on axioms: [") + r"([^\]]*)\]", log, re.S)
        none = f"'{name}' does not depend on any axioms" in log
        if dep:
            used = sorted(a.strip() for a in dep.group(1).replace("\n", " ").split(",") if a.strip())
        elif none:
            used = []
        else:
            raise SystemExit(f"no axiom report for {name}")
        bad = set(used) - ALLOWED
        if bad:
            raise SystemExit(f"{name} uses disallowed axioms {sorted(bad)}")
        axioms[name] = used
    report["axioms"] = axioms
    report["axiom_union"] = sorted({a for used in axioms.values() for a in used})

    # False controls.
    controls = {}
    for path in sorted((ROOT / "FalseControls").glob("*.lean")):
        proc = run(["lake", "env", "lean", str(path.relative_to(ROOT))])
        text = proc.stdout + proc.stderr
        (OUT / f"{path.stem}.log").write_text(text)
        if proc.returncode == 0:
            print(text)
            raise SystemExit(f"false control ACCEPTED: {path.name}")
        if INFRA_FAILURE.search(text) or not MATH_FAILURE.search(text):
            print(text)
            raise SystemExit(f"false control failed for the wrong reason: {path.name}")
        controls[path.stem] = "rejected"
    if len(controls) < EXPECTED_FALSE_CONTROLS:
        raise SystemExit(f"expected {EXPECTED_FALSE_CONTROLS} false controls, found {len(controls)}")
    report["false_controls"] = controls
    report["recorded_submissions"] = check_recorded_submissions()

    (OUT / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"OK: {total} theorems, "
          f"axioms used: {report['axiom_union']}, {len(controls)} false controls rejected")
    return 0


def annotate(message: str) -> None:
    """Surface a failure as a GitHub error annotation (readable without the log)."""
    flat = message.replace("%", "%25").replace("\r", "").replace("\n", "%0A")
    print(f"::error title=verify.py::{flat[:6000]}")


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit as exc:
        if exc.code not in (0, None):
            annotate(str(exc.code) + "%0A" + LAST_OUTPUT[-5000:])
        raise
