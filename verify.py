#!/usr/bin/env python3
"""Build, audit axiom dependencies, and independently check the full theorem.

Exit 0 in default mode means the partial library and axiom audit passed.
--require-complete also requires an unconditional theorem with exactly the
manuscript's hypotheses; until it exists, that mode exits with code 2.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / "verification"

COMPLETE_CHECK = r"""import Broersma
universe u
example {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    (ht : Broersma.ToughThreeHalves G) (hf : Broersma.TwoK2Free G) :
    Broersma.Hamiltonian G := by
  exact Broersma.main G hn ht hf
#print axioms Broersma.main
"""


def run(command: list[str], log: str, stdin: str | None = None) -> subprocess.CompletedProcess:
    result = subprocess.run(
        command, cwd=ROOT, input=stdin, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    (LOGS / log).write_text(result.stdout, encoding="utf-8")
    return result


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    LOGS.mkdir(exist_ok=True)

    meta = json.loads((ROOT / "source" / "metadata.json").read_text())
    snapshot_ok = digest(ROOT / "source" / "v4.tex") == meta["sha256"]
    original = ROOT / meta["original_relative_path"]
    original_ok = not original.exists() or digest(original) == meta["sha256"]

    version = run(["lean", "--version"], "lean-version.txt")
    build = run(["lake", "build"], "build.log")
    if build.returncode:
        print(build.stdout)
        return 1
    audit = run(["lake", "env", "lean", "Audit.lean"], "axioms.log")
    complete = run(["lake", "env", "lean", "--stdin"], "complete-main.log", COMPLETE_CHECK)

    warnings = "warning:" in build.stdout or "warning:" in audit.stdout
    audit_ok = audit.returncode == 0 and "AXIOM AUDIT PASSED" in audit.stdout
    partial_ok = snapshot_ok and original_ok and audit_ok and not warnings
    full_ok = partial_ok and complete.returncode == 0
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_sha256": meta["sha256"],
        "snapshot_matches": snapshot_ok,
        "original_matches_if_present": original_ok,
        "lean": version.stdout.strip(),
        "build_exit_code": build.returncode,
        "axiom_audit_exit_code": audit.returncode,
        "warnings": warnings,
        "partial_library_verified": partial_ok,
        "complete_main_exit_code": complete.returncode,
        "complete_main_verified": full_ok,
        "status": "COMPLETE" if full_ok else "PARTIAL" if partial_ok else "FAILED",
        "main_proof_obligation": "Broersma.InternalConstruction",
        "external_axioms": [
            "Broersma.External.split_hamiltonian",
            "Broersma.External.two_factor",
            "Broersma.External.coabsorbable_successors",
            "Broersma.External.chvatal_properties",
        ],
    }
    (LOGS / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(version.stdout.strip())
    print("Library build and axiom audit:", "PASS" if partial_ok else "FAIL")
    print("Unconditional main theorem:", "PASS" if full_ok else "NOT PROVED")
    print("Status:", report["status"])
    print("Detailed logs:", LOGS)
    if not partial_ok:
        print(audit.stdout)
        return 1
    if args.require_complete and not full_ok:
        print("Full verification requires Broersma.main with no InternalConstruction premise.")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
