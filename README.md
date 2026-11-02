# Radial uniqueness of the nonzero 1-points of J₀

Paper and accompanying Lean proofs by Helen W. J. Zhang and Chengdong Zhao.

**[Read the paper (PDF)](paper/j0_radial_uniqueness.pdf)** ·
[LaTeX source](paper/main.tex) ·
[Statement correspondence and verification supplement (ZIP)](paper/final-supplement.zip)

The final manuscript contains sixteen numbered results and 118 retained
mathematical inventory items, including Introduction A/B/C and the supporting
identities. The formalization covers the radial escape estimate, raywise
uniqueness, and the local and global two-radius results. The code also retains
two additional geometric counterexamples from the original formalization scope.

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

The [final supplement](paper/final-supplement.zip) contains
`retained-correspondence.json`, which maps the current manuscript's 118 items to
248 Lean roots, their actual types, definition bodies and proof evidence. It
also includes the separately checked positive-polar-radius bridge for
Proposition 5.1. The repeated summary in the abstract, lines 60–61 of
[`main.tex`](paper/main.tex#L60), is covered by the supplement's `N5.1` and
`P5.1-DELTA-PROPAGATE` entries and the Lean declarations
`paper_5_1`, `ray_separation`, and `radial_derivative_decomposition`.

Extract the supplement **outside the code checkout**. Its verifier is bound to
the fixed proof commit `00d977912114c7fffb189e85051914685dcee5e6` (release
`v1.0.0`). Use a separate checkout at that commit, or extract the supplement's
`fixed-code-source.zip`; fetch the pinned dependencies as described above. Run
from the extracted supplement directory:

```sh
python3 verify_supplement.py --code-root /path/to/fixed-code --manuscript /path/to/main.tex
```

This read-only command checks the package and source bindings. The supplement
README gives live Lean replay commands. Its sealed reports describe the
pre-publication verification snapshot; this publication does not rewrite them.
The new `main` commit publishes the paper and updates documentation, so it is
not the fixed checkout expected by that supplement verifier.

The root-level [`correspondence.md`](correspondence.md),
[`correspondence.json`](correspondence.json), and
[`dependency_closures.json`](dependency_closures.json) preserve the historical
120-item baseline, including the two additional geometric examples. Their
source line numbers refer to that baseline manuscript. The unchanged proof
source hashes and review provenance are in
[`evidence/baseline.json`](evidence/baseline.json).

Kernel verification and mathematical correspondence are distinct checks. The
public checker performs source and kernel verification. The manuscript wording,
definitions, and proof correspondence were reviewed separately; publication
metadata in [`PUBLICATION.json`](PUBLICATION.json) records the current
manuscript, PDF and supplement hashes. All 193 Lean source files and the fixed
`v1.0.0` proof release remain unchanged.

## Cite

Helen W. J. Zhang and Chengdong Zhao. *Formal proofs accompanying Radial
Uniqueness of the Nonzero 1-Points of J0*, version 1.0.0 (2026).
[Fixed release](https://github.com/VerMoriarty/j0-radial-uniqueness/releases/tag/v1.0.0).
Machine-readable metadata is provided in [`CITATION.cff`](CITATION.cff).
