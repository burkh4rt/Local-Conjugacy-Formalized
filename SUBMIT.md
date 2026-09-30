# Reviewing and submitting this snapshot

Prepared against
[Palomar's instructions](https://palomar-registry.org/how-to-submit) on
2026-09-30 and the exact preprint arXiv:2609.37678v1. The checked minimum
toolchain is v4.35.0-rc2, which is pinned here with matching Mathlib. Recheck the
requirements at submission time.

1. Review [Challenge.lean](Challenge.lean), using
   [the read-back](docs/read-back.md) and the unchanged TeX in `sources/`. The
   Challenge is the statement of record and imports Mathlib alone. Check the
   group/cohomology definitions, finite hypotheses, action conventions, and both
   concrete counterexamples. Only after completing your review should you update
   `review` in `formalization.yaml` to say it is author-verified.
2. Run `lake exe cache get` followed by `bash scripts/check.sh`. Its thirteen
   intentional Challenge holes are expected. The Solution and all local
   supporting proofs must depend only on the three standard Lean axioms. The
   local audit compares types and shared definition bodies in separate
   environments; it is not the official Comparator.
3. Optionally reproduce the local macOS comparison with
   `bash scripts/run-local-comparator.sh`. It uses the documented unsandboxed
   mode with Lean, NanoDa and con-ron, and is distinguished from the official
   verifier. On Linux with Bubblewrap, run `bash scripts/run-comparator.sh`, or
   use the supplied GitHub workflow. It follows PalomarTemplate's current local
   verifier recipe. The website/policy and template differ in their description
   of trusted-tool provisioning; Palomar supplies its own verifier tools. The
   successful local unsandboxed replay is recorded in
   `reports/local-comparator-validation.json`. No remote or sandboxed run is
   claimed. Keep the submitted `comparator.json` unchanged: it selects thirteen
   names, no definition holes, and only the three standard axioms.
4. Publish this folder as the root of a public GitHub repository with its
   license, manifest, metadata, source, and scripts, then record the exact
   40-character commit SHA. Do not publish `.lake/`. The older local project is
   not a source dependency. This directory is the substantive development, not a
   wrapper around an unpublished proof repository.
5. Submit the repository and fixed commit through Palomar, identify your actual
   author/maintainer relationship, and retain the returned status link. Use
   default paths if this folder is the repository root. If it is nested, select
   project path `Local-Conjugacy-Formalized`, the corresponding Comparator and
   metadata paths, and retain a repository-root license. Palomar scans the entire
   submitted repository for Lean source requirements, so publishing this folder
   alone avoids unrelated historical drafts.

The [human form](https://submit.palomar-registry.org/) and the
[agent protocol](https://submit.palomar-registry.org/llms.txt) are different
routes; an automated submitter should use the protocol, not drive the form.
Registration is a subsequent explicit decision after verification and review. No
repository has been published and no submission or registration has been made as
part of preparing this folder.

All `.lean` files use the module system and remain below the 10,000-line per-file
limit. Challenge is below the hard limits of 1,000 lines and 100 KiB, and below
the preferred 32 KiB, but exceeds the preferred 300 lines because it exposes
ordinary definitions for all thirteen results. This incurs a review-size warning
rather than violating the hard source limit.
