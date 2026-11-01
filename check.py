"""Rebuild and audit the fixed public Lean source release (Python 3.10+)."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CLAIMS = {"2.1", "2.2", "2.3", "2.4", "3.1", "3.2", "4.1", "4.2",
          "5.1", "5.2", "5.3", "6.1", "6.2", "6.3", "6.4", "6.5"}
ANCILLARY = {
    "mu_moments", "k0_series_convergence", "k0_connection", "laplace_integrability",
    "amplitude_integrability", "factorization", "circle_mean_well_defined",
    "distribution_laplacian_bridge", "weyl_regularization", "all_radius_mean_value",
    "boundary_finite_smooth_counterexample", "subcritical_smooth_counterexample",
    "real_bessel_integral", "k0_boundary_connection", "k0_cosh_integral", "paper_complete",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def source_check(root=ROOT):
    manifest = json.loads((root / "SOURCE_MANIFEST.json").read_text())
    baseline = json.loads((root / "evidence/baseline.json").read_text())
    for name, digest in manifest["files_sha256"].items():
        rel = Path(name)
        require(not rel.is_absolute() and ".." not in rel.parts, "Unsafe manifest path")
        path = root / rel
        require(path.is_file() and not path.is_symlink() and sha(path) == digest,
                "Source hash mismatch: " + name)
    expected = baseline["all_lean_files_sha256"]
    actual = {str(p.relative_to(root)) for p in root.rglob("*.lean")
              if not any(part in {".lake", ".git", "CHECK_RUNS"} for part in p.relative_to(root).parts)}
    require(actual == set(expected), "Lean source inventory differs from the verified baseline")
    for name, digest in expected.items():
        require(sha(root / name) == digest, "Verified Lean source changed: " + name)
    require(baseline["expected_modules"] == 189 and baseline["expected_declarations"] == 2984,
            "Unexpected verification baseline")
    require(set(baseline["permitted_axioms"]) == ALLOWED, "Axiom policy changed")
    return manifest, baseline


def validate_reflection(data, baseline):
    modules = {".".join(Path(n).with_suffix("").parts)
               for n in baseline["accepted_lean_sources_sha256"]}
    require(len(data["modules"]) == len(modules) and set(data["modules"]) == modules,
            "Reflected module inventory mismatch")
    rows = data["declarations"]
    names = {row["name"] for row in rows}
    require(len(rows) == baseline["expected_declarations"] and len(names) == len(rows),
            "Missing, additional or duplicate reflected declarations")
    for key, expected in [("claims", CLAIMS), ("ancillary_obligations", ANCILLARY)]:
        targets = data[key]
        require(len(targets) == len(expected) and {row["id"] for row in targets} == expected,
                "Missing or additional targets: " + key)
        for row in targets:
            require(row["status"] == "closed" and row["type_matches"] and row["kind"] == "theorem",
                    "Exact quantified target failed: " + row["id"])
            require(not row["unexpected_axioms"] and set(row["axioms"]) <= ALLOWED,
                    "Unproved target input: " + row["id"])
    for name in data["all_imported_modules"]:
        require(not ((name.startswith(("Definitions.", "Solutions.")) and name not in modules)
                     or name == "Theorems" or name.startswith("Theorems.")),
                "Unexpected local import: " + name)
    for row in rows:
        require(row["kind"] != "axiom" and not row["unexpected_axioms"]
                and set(row["axioms"]) <= ALLOWED, "Unproved declaration input: " + row["name"])
    require(set(baseline["required_named_roots"]) <= names, "A correspondence root is missing")


def atomic_json(path, data):
    temporary = path.with_name(path.name + ".tmp-" + uuid.uuid4().hex)
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true", help="check hashes only; does not certify a build")
    args = parser.parse_args()
    run_id = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ") + "-" + uuid.uuid4().hex[:8]
    folder = ROOT / "CHECK_RUNS" / run_id
    folder.mkdir(parents=True)
    latest = ROOT / "CHECK_RESULT.json"
    atomic_json(latest, {"status": "running", "run_id": run_id})
    environment = os.environ.copy()
    for key in ["LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN"]:
        environment.pop(key, None)

    def run(label, command):
        print(label, flush=True)
        process = subprocess.run(command, cwd=ROOT, env=environment, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (folder / (label + ".log")).write_text(process.stdout)
        require(process.returncode == 0, label + " failed:\n" + process.stdout[-12000:])
        return process.stdout

    try:
        manifest, baseline = source_check()
        if args.source_only:
            result = {"status": "source_only_passed", "scope": "source hashes only; no kernel rebuild"}
        else:
            version = run("toolchain", ["lake", "env", "lean", "--version"])
            require(re.search(r"\bversion 4\.33\.1\b", version), "Actual Lean toolchain mismatch")
            packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
            for package in packages:
                path = str(ROOT / ".lake/packages" / package["name"])
                head = run("dependency-" + package["name"], ["git", "-C", path, "rev-parse", "HEAD"]).strip()
                require(head == package["rev"], "Dependency revision mismatch: " + package["name"])
                dirty = run("dependency-tree-" + package["name"],
                            ["git", "-C", path, "status", "--porcelain", "--untracked-files=no"]).strip()
                require(not dirty, "Dependency tracked tree modified: " + package["name"])
            run("build", ["lake", "build"])
            output = run("reflection", ["lake", "env", "lean", "Audit.lean"])
            rows = [line.split("\t", 1)[1] for line in output.splitlines()
                    if line.startswith("P2M_J0_AUDIT_JSON\t")]
            require(len(rows) == 1, "Missing or duplicate environment reflection")
            reflected = json.loads(rows[0])
            validate_reflection(reflected, baseline)
            source_check()
            result = {"status": "passed", "scope": "fixed source, exact Lean targets and transitive axioms",
                      "numbered_results": len(CLAIMS), "supporting_targets": len(ANCILLARY),
                      "actual_modules": len(reflected["modules"]),
                      "actual_declarations": len(reflected["declarations"]),
                      "allowed_axioms": sorted(ALLOWED), "dependency_revisions_checked": len(packages),
                      "manuscript_semantics": "separate reviewed correspondence; not rerun by this public kernel checker"}
        result.update(run_id=run_id, source_manifest_sha256=sha(ROOT / "SOURCE_MANIFEST.json"),
                      checked_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    except BaseException as error:
        result = {"status": "failed", "run_id": run_id, "error": str(error),
                  "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
        with (folder / "result.json").open("x") as stream:
            json.dump(result, stream, indent=2)
        atomic_json(latest, result)
        raise
    else:
        with (folder / "result.json").open("x") as stream:
            json.dump(result, stream, indent=2)
        atomic_json(latest, result)
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
