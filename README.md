# Local conjugacy in prosolvable groups

Lean 4 formalization of Burkhart's
[arXiv:2609.37678v1](https://arxiv.org/abs/2609.37678v1), prepared for Palomar.
All eleven numbered results (including Lemma 1.2) and both Introduction
counterexamples are compared declarations in the namespace `LocalConjugacy`.

M.C.B. has completed human review, personally verified the submission, and read
[Challenge.lean](Challenge.lean). The agent's
[read-back against arXiv v1](docs/read-back.md) documents the statement
comparison. The [proof correspondence](docs/manuscript-correspondence.md) maps
every result to its proof and explains the proof adaptations.
[The exact arXiv source](sources/local-conjugacy-prosolvable-re.tex) and its
original downloaded archive are included unchanged. Its bibliography is embedded
in the TeX. The [source inventory](reports/source-result-inventory.json) records
every numbered statement and its source line.

Theorem 1.1 concerns locally conjugate closed supplements of an arbitrary closed
normal pronilpotent subgroup. Lemma 1.2 gives a pointed bijection on actual
continuous nonabelian cohomology quotients. Propositions 2.1–2.2 allow infinite
locally finite discrete coefficients; Proposition 2.3 and Propositions 3.1–3.2
have finite kernels or coefficients as stated in v1. The inclusion and
fixed-point results keep every closedness, transitivity, normality, and
supplement hypothesis of the preprint.

The quaternion example includes an isomorphism with `GL(2,3)`, exactly two
cohomology classes, trivial Sylow cohomology, and actual locally conjugate but
nonconjugate complements. The second example explicitly identifies the wreath
product, its Heisenberg subgroup, the cyclic complement of order six, and the
subgroup `C₃ × S₃`, and proves the failure of global inclusion.

The full build and audit passed. The local unsandboxed Comparator also passed,
with Lean, NanoDa, and con-ron accepting the exported proof; see
[verification evidence](reports/README.md). Human statement review is complete;
Palomar's official sandboxed run remains pending.

The proof development contains no admitted proofs or custom axioms.
`Challenge.lean` imports Mathlib alone and deliberately leaves thirteen target
proofs as `sorry`. `Solution.lean` imports the proved development and does not
import Challenge. The metadata records the completed human verification of
definitions and statements as `author-verified`.

The pinned versions are Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. From a clean checkout with Elan:

```sh
lake exe cache get
bash scripts/check.sh
```

This builds the sources, checks the independent statement file, validates
metadata, compares exact compiled theorem types, shared definitions and helper
proofs in separate Lean environments, and audits all local proof declarations for
transitive axioms. The only permitted axioms are `propext`, `Classical.choice`,
and `Quot.sound`. Results are in
[reports/validation.json](reports/validation.json). On macOS,
`bash scripts/run-local-comparator.sh` runs Comparator with Lean, NanoDa, and
con-ron without the Linux sandbox. On Linux, `bash scripts/run-comparator.sh`
runs the sandboxed version. Local results do not replace Palomar's official
verification.

[SUBMIT.md](SUBMIT.md) describes review and publication steps. This folder
contains the substantive proof development, with no dependency on the older local
project. A local ignored `.lake` cache may reuse installed dependencies. The
development adapts `../lcp-formalized`; fingerprints and inherited attributions
are recorded in `reports/` and [NOTICE](NOTICE). The code is Apache-2.0; the
preprint retains its own copyright. No publication or Palomar submission has been
performed.
