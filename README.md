# Radial uniqueness of the nonzero 1-points of J₀

Lean proofs accompanying the paper by Helen W. J. Zhang and Chengdong Zhao.
The formalization includes all sixteen numbered results, the supporting analytic
identities, the local and global two-radius results, and both geometric
counterexamples in Remark 6.6.

## Reproduce

Install [elan](https://github.com/leanprover/elan) and Python 3.10 or later. From a
clean clone of this repository, run:

```sh
lake exe cache get
python3 check.py
```

The toolchain is **Lean 4.33.1**. The exact mathlib revision is
`0df444a360eaa60ab8c11dca51a86af692955474`; all ten dependency revisions are fixed
in `lake-manifest.json` and checked against their actual Git checkouts.

The checker builds the supplied modules and reflects the elaborated Lean
environment, including private and generated declarations. It checks sixteen
independently written quantified targets, sixteen supporting targets, and all
transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
Each attempt writes a fresh `CHECK_RESULT.json` and a separate record under
`CHECK_RUNS/`; failures do not leave an earlier PASS current.

`python3 check.py --source-only` checks only source hashes and must not be read as
a successful Lean rebuild.

## Paper correspondence

The main entry point is
[`Solutions.J0RadialUniqueness.RevisionVerified`](Solutions/J0RadialUniqueness/RevisionVerified.lean).
[`Verified.lean`](Solutions/J0RadialUniqueness/Verified.lean) assembles the sixteen
numbered results. The geometric counterexamples are checked separately by
[`Audit.lean`](Audit.lean).

[`correspondence.md`](correspondence.md) and
[`correspondence.json`](correspondence.json) identify all 120 mathematical items,
their full Lean types and actual proof evidence.
[`dependency_closures.json`](dependency_closures.json) records the dependency
closures. Source line numbers refer to the companion manuscript, which is
distributed separately. The proof sources and auditor are byte-identical to the
independently reviewed source archive; their hashes and review provenance are in
[`evidence/baseline.json`](evidence/baseline.json).

Kernel verification and mathematical correspondence are distinct checks. The
public checker performs source and kernel verification. The manuscript wording,
definitions, and proof correspondence were reviewed separately; publication
metadata records the corresponding manuscript hash. The paper PDF and TeX are
not included in this code repository.

## Cite

Helen W. J. Zhang and Chengdong Zhao. *Formal proofs accompanying Radial
Uniqueness of the Nonzero 1-Points of J0*, version 1.0.0 (2026).
[Fixed release](https://github.com/VerMoriarty/j0-radial-uniqueness/releases/tag/v1.0.0).
Machine-readable metadata is provided in [`CITATION.cff`](CITATION.cff).
