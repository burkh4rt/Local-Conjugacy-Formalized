# Verification evidence

The final local checks passed on 2026-09-30 for Lean v4.35.0-rc2 and Mathlib
commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

| Check                                   | Result                                                                          | Evidence                                                   |
| --------------------------------------- | ------------------------------------------------------------------------------- | ---------------------------------------------------------- |
| Full Lake build                         | Passed                                                                          | `final-check.log`                                          |
| Compared result coverage                | All eleven numbered results and both counterexamples                            | `source-result-inventory.json`, `../comparator.json`       |
| Exact compiled statement types          | 13/13 match, including universe-parameter names                                 | `validation.json`                                          |
| Shared definition bodies                | 94 match                                                                        | `validation.json`                                          |
| Shared helper proof terms               | 66 match                                                                        | `validation.json`                                          |
| Transitive local proof axioms           | 926 supporting theorem declarations; only propext, Classical.choice, Quot.sound | `validation.json`                                          |
| Local Comparator                        | Passed                                                                          | `local-comparator.log`, `local-comparator-validation.json` |
| Lean default kernel                     | Accepted                                                                        | `local-comparator.log`                                     |
| NanoDa                                  | Accepted                                                                        | `local-comparator.log`                                     |
| con-ron                                 | Accepted 28,033 declarations                                                    | `local-comparator.log`                                     |
| Source layout and preprint fingerprints | Passed                                                                          | `source-layout.json`, `source-fingerprints.json`           |
| Pinned dependency checkouts             | Nine match their recorded commits; no tracked modifications                     | `dependency-pins.json`                                     |
| Metadata and configuration              | Passed project-specific validation                                              | `final-check.log`                                          |

The Comparator run used `--inadvisably-no-sandbox` on macOS. It does not have the
isolation guarantees of Palomar's Linux sandbox and is not an official registry
verification. Reproduce it with `bash scripts/run-local-comparator.sh`. The
separate `scripts/run-comparator.sh` and GitHub workflow provide the sandboxed
Linux route. No remote CI or official Palomar run is claimed.

`validation.json` records the compiled-type/definition/helper/axiom audit only.
Its `full_comparator_run`, `nanoda_run`, and `con_ron_run` flags are false
because that script itself does not run the kernels. The subsequent successful
kernel replay has its own hash-bound `local-comparator-validation.json`.
`submission_ready: false` also preserves the pending human statement review and
official submission workflow; it does not indicate an omitted target proof.

The independent Challenge has thirteen deliberate `sorry` proof holes. They are
expected by the Challenge/Solution workflow and occur in no Solution proof. The
noncompiled blueprint is a statement template. The proof dependency audit found
no `sorryAx`, `Lean.ofReduceBool`, or custom axiom.

The local audit was strengthened during preparation after Comparator exposed an
inherited universe-name mismatch and module-private generated helper proofs.
Those issues were fixed and the final full comparison passed. The final log and
source hashes, rather than older development checks, are the evidence for this
snapshot.

The agent's mathematical read-back is `../docs/read-back.md`. It remains separate
from machine checking. Michael C. Burkhart's planned human review is pending, and
no publication, Palomar submission, or registration has occurred.
