
#!/usr/bin/env python3
# SCRIPT: COXETER-RANK2-LEAN-GATE-01
"""Gate a candidate proof file for the rank-two classification targets.

A submission is a single Lean file that imports `Targets` and proves the frozen
statements of `swarm/Statements.lean`. This script decides, mechanically, whether it
may be accepted. Each check exists to close one way a submission can look right and
be wrong:

1. Banned tokens. `sorry`, `admit`, `native_decide`, a declared `axiom`, `unsafe`,
   `opaque` or `maxHeartbeats` are all ways to be accepted without a proof. They are
   refused by name before Lean is even run.

2. Statement parity. The text of every theorem statement must equal the frozen text
   in `swarm/Statements.lean` up to whitespace. A proof of a weaker statement is
   worth nothing, and a plausible-looking submission that quietly weakens a
   hypothesis (`1 ≤ a` to `0 < a`, `≤ 3` to `< 4`) is the common failure.

3. Compilation. `lean` must accept the file. This is the ordinary check; it is not
   enough on its own, because Lean accepts `sorry` with a warning.

4. Kernel replay. `leanchecker` re-checks every declaration in the module with the
   separate kernel checker, so a bug in the elaborator cannot smuggle a proof in.

5. Axiom audit. `#print axioms` on every theorem must report a subset of
   {propext, Classical.choice, Quot.sound}. This catches `sorryAx` in a helper the
   author forgot, a hidden axiom, and `Lean.ofReduceBool` from `native_decide`.

6. False control. Each file in `swarm/FalseControls/` states something false about
   these definitions and must fail to compile for a mathematical reason. If the
   checker accepts one, the checker is broken.

Definitions are not part of the submission: `swarm/Targets.lean` is compiled by this
script from the repository, and a submission imports it, so a member cannot redefine
`cartan` or `titsForm` underneath the statement.

Statement extraction compares text from `theorem <name>` to the first `:=`. A statement
that contains a `:=` inside its type (a `let`, a structure literal) would be compared on
a truncated prefix; the frozen statements contain none, and a changed one is rejected
rather than passed.

Usage:
    python3 scripts/gate.py --submission candidate.lean           # full acceptance
    python3 scripts/gate.py --submission candidate.lean --partial # during work
Exit status 0 means every check passed; 1 means at least one failed (see the report).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VERIFY = os.path.join(ROOT, "verification")
BUILD = os.path.join(VERIFY, "build")
WORK = os.path.join(VERIFY, "work")
STATEMENTS = os.path.join(ROOT, "swarm", "Statements.lean")
TARGETS = os.path.join(ROOT, "swarm", "Targets.lean")
CORE = os.path.join(ROOT, "RankTwoCertificate.lean")
CONTROLS = os.path.join(ROOT, "swarm", "FalseControls")
REPORT = os.path.join(VERIFY, "gate-report.json")

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAMESPACE = "OperatorFirst.CoxeterRankTwo"

PIN_FILE = os.path.join(ROOT, "lean-toolchain")
MATHLIB_PIN_FILE = "/opt/mathlib/lean-toolchain"

THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)",
    re.M)
PROTECTED_RE = re.compile(r"private\s+(?:theorem|lemma)")
BANNED = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bdecide\s*\+native\b", "decide +native"),
    (r"^\s*axiom\s", "declared axiom"),
    (r"\bopaque\s+(?:def|theorem)\b", "opaque"),
    (r"\bunsafe\b", "unsafe"),
    (r"\bimplemented_by\b", "implemented_by"),
    (r"\bpartial\s+(?:def|theorem)\b", "partial definition"),
    (r"\bLean\.ofReduceBool\b", "Lean.ofReduceBool"),
    (r"\bset_option\s+maxHeartbeats\b", "maxHeartbeats override"),
    (r"\bset_option\s+autoImplicit\s+true\b", "autoImplicit reintroduced"),
]
MATH_FAILURE = re.compile(
    r"unsolved goals|proved that the proposition.*false|tactic '.*' failed|"
    r"linarith failed|failed to prove|decide failed|norm_num failed|type mismatch|"
    r"made no progress|failed to simplify|omega.*failed|not a definitional equality",
    re.S | re.I)
INFRA_FAILURE = re.compile(
    r"unknown (?:module|identifier|constant|namespace)|unexpected token|"
    r"object file .* does not exist|invalid field|already declared", re.I)


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def lean_env(*dirs: str) -> dict:
    env = dict(os.environ)
    parts = [d for d in dirs if d]
    base = env.get("LEAN_PATH", "")
    if base:
        parts.append(base)
    env["LEAN_PATH"] = os.pathsep.join(parts)
    return env


class Result:
    def __init__(self) -> None:
        self.log: list[str] = []

    def run(self, argv: list[str], cwd: str = ROOT, env: dict | None = None,
            timeout: int = 1800) -> subprocess.CompletedProcess:
        started = time.time()
        proc = subprocess.run(argv, cwd=cwd, env=env or dict(os.environ),
                              capture_output=True, text=True, timeout=timeout)
        self.log.append(f"$ {' '.join(argv)}  (cwd={cwd}, {time.time() - started:.1f}s, "
                        f"exit {proc.returncode})\n{proc.stdout}{proc.stderr}")
        return proc


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"^[ \t]*--[^\n]*$", " ", text, flags=re.M)


def statements(text: str) -> list[tuple[str, str]]:
    """(name, normalised statement text) for every theorem/lemma, in file order."""
    clean = strip_comments(text)
    out: list[tuple[str, str]] = []
    for match in THEOREM_RE.finditer(clean):
        name = match.group(1)
        tail = clean[match.end():]
        cut = tail.find(":=")
        chunk = tail if cut < 0 else tail[:cut]
        normalised = " ".join(chunk.split())
        out.append((name, normalised))
    seen: dict[str, int] = {}
    for name, _ in out:
        seen[name] = seen.get(name, 0) + 1
    dupes = sorted(n for n, k in seen.items() if k > 1)
    if dupes:
        raise SystemExit(f"duplicate theorem names in submission: {dupes}")
    return out


def read_lean_version(text: str) -> str | None:
    match = re.search(r"v?(\d+\.\d+\.\d+)", text or "")
    return match.group(1) if match else None


def environment_notes(runtime_lean: str) -> dict:
    """Record whether this VM's toolchain is the repository's pin.

    The gate is a fast local filter; the repository's CI (`lake build` + `verify.py`
    under the pinned toolchain) is the pin-authoritative check. A proof accepted here
    under a different Lean is therefore reported as such, never as pin-exact.
    """
    pin = read_lean_version(open(PIN_FILE).read()) if os.path.exists(PIN_FILE) else None
    runtime = read_lean_version(runtime_lean)
    mathlib_pin = (read_lean_version(open(MATHLIB_PIN_FILE).read())
                   if os.path.exists(MATHLIB_PIN_FILE) else None)
    notes = {"runtime_lean": runtime, "repo_pin": pin, "mathlib_pin": mathlib_pin,
             "pin_match": runtime is not None and runtime == pin}
    if not notes["pin_match"]:
        notes["warning"] = (
            f"checked under Lean {runtime} (this VM) but the repository pins {pin}: "
            f"a PASS here is not pin-exact. The CI workflow re-checks under the pin.")
    return notes


def banned_hits(text: str) -> list[str]:
    clean = strip_comments(text)
    hits = []
    for pattern, label in BANNED:
        if re.search(pattern, clean, flags=re.M):
            hits.append(label)
    return hits


def prepare(result: Result) -> dict:
    """Compile the frozen definitions from the repository into verification/build."""
    os.makedirs(BUILD, exist_ok=True)
    os.makedirs(WORK, exist_ok=True)
    manifest_path = os.path.join(BUILD, "manifest.json")
    lean_version = result.run(["lean", "--version"], cwd=BUILD).stdout.strip()
    hashes = {
        "lean": lean_version,
        "RankTwoCertificate": sha256(CORE),
        "Targets": sha256(TARGETS),
        "Statements": sha256(STATEMENTS),
    }
    have = {}
    if os.path.exists(manifest_path):
        try:
            have = json.load(open(manifest_path))
        except json.JSONDecodeError:
            have = {}
    complete = (have == hashes
                and os.path.exists(os.path.join(BUILD, "RankTwoCertificate.olean"))
                and os.path.exists(os.path.join(BUILD, "Targets.olean")))
    if complete:
        return {**hashes, "cache": "hit"}

    env = lean_env(BUILD)
    for source, module in ((CORE, "RankTwoCertificate"), (TARGETS, "Targets")):
        shutil.copy(source, os.path.join(BUILD, module + ".lean"))
        proc = result.run(["lean", "-o", module + ".olean", module + ".lean"],
                          cwd=BUILD, env=env)
        if proc.returncode != 0:
            raise SystemExit(f"cannot compile frozen definitions from {source}:\n"
                             f"{proc.stdout}{proc.stderr}")
    json.dump(hashes, open(manifest_path, "w"), indent=2)
    return {**hashes, "cache": "miss"}


def parse_axioms(output: str, name: str) -> list[str] | None:
    match = re.search(re.escape(f"'{name}' depends on axioms: [") + r"([^\]]*)\]",
                      output, re.S)
    if match:
        return sorted(a.strip() for a in match.group(1).replace("\n", " ").split(",")
                      if a.strip())
    if f"'{name}' does not depend on any axioms" in output:
        return []
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--submission", required=True, help="candidate .lean file")
    parser.add_argument("--partial", action="store_true",
                        help="accept a submission that covers a subset of the targets")
    parser.add_argument("--strict-pin", action="store_true",
                        help="fail if this VM's Lean differs from the repository pin")
    args = parser.parse_args()

    submission = os.path.abspath(args.submission)
    if not os.path.exists(submission):
        raise SystemExit(f"no such file: {submission}")

    result = Result()
    report: dict = {"script": "COXETER-RANK2-LEAN-GATE-01", "checks": {}, "submission": {
        "path": submission, "sha256": sha256(submission)}}

    prepared = prepare(result)
    report["frozen"] = prepared
    report["environment"] = environment_notes(prepared["lean"])

    source = open(submission, encoding="utf-8").read()

    # 1. banned tokens
    hits = banned_hits(source)
    report["checks"]["banned_tokens"] = {"ok": not hits, "hits": hits}

    # 2. statement parity
    canonical = statements(open(STATEMENTS, encoding="utf-8").read())
    submitted = dict(statements(source))
    changed = [n for n, text in canonical
               if n in submitted and submitted[n] != text]
    missing = [n for n, _ in canonical if n not in submitted]
    extra = [n for n in submitted if n not in dict(canonical)]
    parity_ok = not changed and (args.partial or not missing)
    report["checks"]["statement_parity"] = {
        "ok": parity_ok, "changed": changed, "missing": missing, "extra": extra,
        "targets": len(canonical), "covered": len(canonical) - len(missing)}

    # 3. compile
    shutil.copy(submission, os.path.join(WORK, "Submission.lean"))
    env = lean_env(WORK, BUILD)
    proc = result.run(["lean", "-o", "Submission.olean", "Submission.lean"],
                      cwd=WORK, env=env)
    compile_ok = proc.returncode == 0
    lines = (proc.stdout + proc.stderr).splitlines()
    errors = [l for l in lines if ": error" in l]
    report["checks"]["compile"] = {"ok": compile_ok,
                                   "errors": errors[:20],
                                   "sorry_warnings": sum("declaration uses `sorry`" in l
                                                         for l in lines)}

    # 4. kernel replay
    replay_ok = False
    if compile_ok:
        rep = result.run(["leanchecker", "Submission"], cwd=WORK, env=env)
        replay_ok = rep.returncode == 0
        report["checks"]["kernel_replay"] = {
            "ok": replay_ok,
            "tail": (rep.stdout + rep.stderr).strip().splitlines()[-5:]}

    # 5. axiom audit
    #
    # The targets are audited by their public names. Helpers are audited too when their
    # names resolve, but a `private` helper has a mangled internal name, so naming it
    # fails to elaborate. That is the gate's problem, not the author's: fall back to
    # auditing the targets alone, which is sound because an axiom used by a helper is
    # inherited by every theorem that reaches it.
    axioms_ok = False
    audited: dict[str, list[str]] = {}
    if compile_ok:
        names = [f"{NAMESPACE}.{n}" for n, _ in
                 statements(open(STATEMENTS, encoding="utf-8").read())
                 if n in submitted]
        helpers = [f"{NAMESPACE}.{n}" for n, _ in statements(source)
                   if n not in dict(canonical)]
        bad: list[str] = []
        note = ""
        log = ""
        fallback_used = False
        attempts = ((names + helpers, False), (names, True)) if helpers \
            else ((names, False),)
        for attempt, is_fallback in attempts:
            audit = "\n".join(["import Submission"] +
                              [f"#print axioms {n}" for n in attempt]) + "\n"
            with open(os.path.join(WORK, "Audit.lean"), "w") as f:
                f.write(audit)
            ap = result.run(["lean", "-o", "Audit.olean", "Audit.lean"], cwd=WORK, env=env)
            log = ap.stdout + ap.stderr
            if ap.returncode == 0:
                fallback_used = is_fallback
                if fallback_used and helpers:
                    note = (f"{len(helpers)} helper declaration(s) not auditable by name "
                            f"(private or mangled); their axioms are covered transitively "
                            f"through the audited targets")
                break
        if ap.returncode == 0:
            for name in attempt:
                used = parse_axioms(log, name)
                if used is None:
                    bad.append(f"{name}: no axiom report (namespace or name changed?)")
                elif set(used) - ALLOWED_AXIOMS:
                    bad.append(f"{name}: {sorted(set(used) - ALLOWED_AXIOMS)}")
                else:
                    audited[name] = used
        else:
            bad.append(f"audit file did not compile: {log.strip()[:600]}")
        axioms_ok = ap.returncode == 0 and not bad
        report["checks"]["axioms"] = {"ok": axioms_ok, "problems": bad,
                                      "audited": audited, "note": note}

    # 6. false controls
    controls: dict[str, str] = {}
    controls_ok = True
    if os.path.isdir(CONTROLS):
        for name in sorted(os.listdir(CONTROLS)):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(CONTROLS, name)
            shutil.copy(path, os.path.join(WORK, name))
            cp = result.run(["lean", name], cwd=WORK, env=env)
            text = cp.stdout + cp.stderr
            if cp.returncode == 0:
                controls[name] = "ACCEPTED (gate is broken)"
                controls_ok = False
            elif INFRA_FAILURE.search(text) and not MATH_FAILURE.search(text):
                controls[name] = "failed for an infrastructural reason"
                controls_ok = False
            elif not MATH_FAILURE.search(text):
                controls[name] = "failed for an unrecognised reason"
                controls_ok = False
            else:
                controls[name] = "rejected for a mathematical reason"
    report["checks"]["false_controls"] = {"ok": controls_ok, "results": controls}

    passed = all(check.get("ok") for check in report["checks"].values())
    if args.strict_pin and not report["environment"].get("pin_match"):
        passed = False
    report["verdict"] = "PASS" if passed else "FAIL"
    os.makedirs(VERIFY, exist_ok=True)
    with open(REPORT, "w") as f:
        json.dump(report, f, indent=2, sort_keys=True)
    with open(os.path.join(VERIFY, "gate.log"), "w") as f:
        f.write("\n\n".join(result.log))

    print(f"verdict: {report['verdict']}")
    for name, check in report["checks"].items():
        print(f"  {name:18s} {'ok' if check.get('ok') else 'FAIL'}")
        if not check.get("ok"):
            for key in ("hits", "changed", "missing", "errors", "problems"):
                if check.get(key):
                    print(f"      {key}: {check[key]}")
            if name == "false_controls":
                print(f"      {check.get('results')}")
    cov = report["checks"]["statement_parity"]
    print(f"  targets covered: {cov['covered']}/{cov['targets']}"
          + ("  (partial allowed)" if args.partial else ""))
    env = report["environment"]
    if not env.get("pin_match"):
        print(f"  WARNING: {env.get('warning')}")
    print(f"report: {os.path.relpath(REPORT, ROOT)}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
