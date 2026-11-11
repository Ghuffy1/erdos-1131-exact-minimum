## Submission type

- [x] Mathematical solver information
- [x] Lean proof or formalization author information

## Problem

- Problem ID is JSP-000938, corresponding to Erdős Problem 1131.
- The [original problem](https://www.erdosproblems.com/1131) asks for the minimum ordinary integral of the sum of squared Lagrange cardinal functions over all distinct real nodes in `[-1,1]`, and asks whether `n(2-m_n)` tends to one.
- The [current catalog entry](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/problems/catalog-0901-1000.md#JSP-000938) is Open, Lean proof No, Eligible to claim No. The proposed catalog patch adds the complete-solution submission, fixed proof source, attribution, and manuscript. Existing status and eligibility flags are retained pending maintainer review.
- Related issue is none for this new submission.
- [PR 5133](https://github.com/TheJustinSunPrize/awards/pull/5133) records a sharp-asymptotic publication and remains relevant prior work. The present new contribution is the exact finite-n value construction and its formalization. The earlier coefficient-one disproof by seanm27lol retains its credit. Prior PRs 2496, 3226, and 4514 were checked at preparation. Their scope and mapping differences are described in the verification report.
- The [mathematical paper](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/paper/exact-minimum.pdf) is dated November 11, 2026. Theorem 1.1 states the exact-value construction, attainment, endpoints, and degree bound. Sections 2–7 contain its proof. [The credited asymptotic argument](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/references/seanm27lol-asymptotic-proof.md) supplies the negative answer to the original asymptotic question.

## Formal statement

- Mathematical evidence is the paper and the credited asymptotic source above. Mathematical review by the organizers is pending.
- The [original-formula challenge](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/Challenge.lean) independently writes the cardinal product, unnormalized interval integral, infimum, and both conclusions.
- The fully qualified combined target is `OriginalProblem1131.full_original_problem`. The core construction is `Erdos1131.erdos1131_solution` in [CompleteSolution.lean](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/CompleteSolution.lean).
- Statement origin is a proposed formalization of the original source for maintainer review. [ORIGINAL_PROBLEM.md](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/ORIGINAL_PROBLEM.md) gives the correspondence.
- Every positive node count, arbitrary distinct real nodes, closed endpoints, the ordinary integral, attainment, and the exact value rule are covered. [Submission.lean](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/Submission.lean) proves equality of the two infima and transfers the prior shifted asymptotic result to the original sequence. The theorem assumes only the hypotheses present in the original problem.

## Proof submission

```json
[
  {
    "repository": "https://github.com/Ghuffy1/erdos-1131-exact-minimum",
    "branch": "main",
    "commit": "85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473"
  }
]
```

The original repository is owned by Ghuffy1. The selected proof commit is contained in `main`. The primary entry files are `CompleteSolution.lean`, `Submission.lean`, and `Challenge.lean`. A single-file exact-minimum version is also supplied as `Erdos1131Full.lean`.

## Reproduction

- The exact toolchain is Lean 4.34.1, pinned in [lean-toolchain](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/lean-toolchain).
- Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`. [lake-manifest.json](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/lake-manifest.json) locks the dependency revisions.
- [Reproduction instructions](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/REPRODUCING.md) cover a fresh checkout and all target checks.

```sh
lake exe cache get
lake build
lake env lean Challenge.lean
lake env lean tools/AxiomAudit.lean
lake env lean --run tools/ReplayProof.lean
```

All inspected target and bridge declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The exact outputs and kernel replay evidence are in the report.

## Pre-submission verification

- Checked version is the proof commit identified above. Evidence is provided at the later [verification commit](https://github.com/Ghuffy1/erdos-1131-exact-minimum/tree/d64aff236eb7e63a55e8ac91309150c4a12548b0/verification).
- The [verification report](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/d64aff236eb7e63a55e8ac91309150c4a12548b0/verification/report.md) records actual source and target checks, scope correspondence, dependency revisions, axiom inspection, and kernel replay. It identifies the completed verification levels and their trust boundaries.
- Novelty, absolute first priority, author identity, organizer acceptance, and award eligibility await the appropriate external assessments.

## Attribution

- The new exact-minimum mathematical work and formalization are attributed equally to Will Howe (H0W4RD-dev), Grant Huffman (Ghuffy1), Jensen Kohlmeyer (JENW1N), and Liam Kruer (lkruer).
- Ghuffy1 is the submitting account and repository owner. [AUTHORS.md](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/AUTHORS.md) and [formalization.yaml](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/formalization.yaml) record the team declaration.
- The prior asymptotic disproof and its original formalization are credited to seanm27lol. [THIRD_PARTY.md](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/THIRD_PARTY.md) and the [adaptation record](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/provenance/asymptotic-adaptations.diff) identify the upstream source and the compatibility/integration work.
- AI assistance is acknowledged in the paper and source attribution. Independent human verification is not claimed. Organizer review and the individual identity process remain pending.
- Equal contribution is the authors' declaration. Individual authorship, account-to-author connections, and eligibility for personal claims require organizer confirmation.

## Submission checklist

- [x] The proposed award-repository change contains only the relevant catalog's proof information, attribution, and publication references.
- [x] The submitted result addresses the full original scope. Target and bridge checks are recorded for the fixed proof commit.
- [x] The complete mathematical solution and supporting proof evidence are linked, with the new and prior contributions identified.
- [x] The selected source belongs to the original Ghuffy1 repository, is in the named branch, and has explicit reproduction and axiom-audit evidence.
- [x] The catalog-only change contains no proof source, archives, binaries, vendored dependencies, private identity records, payment data, or delivery details.

This is a submission for mathematical, formal, scope, and attribution review. It makes no award or payment claim.

The submission structure is adapted from The Justin Sun Prize contributors' [contribution template](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/.github/PULL_REQUEST_TEMPLATE.md). The completed problem-specific draft changes its text and is provided under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
