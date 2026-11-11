# Final pre-submission verification

**Verification passed for the stated exact algebraic value formulation at `85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473`.**

The final check was completed at 2026-11-11T22:56:25.044939+00:00. The current prize rules were rechecked at `b1bfe454d37db2838ef76756830aeb23c40de95e`. The prepared repository at `04c5b158a3044f8f1dfd1467245b901c0c3ff9f1` passed the ownership, privacy, source-hash, author, manuscript, citation-schema, fixed-link, and catalog-patch checks.

| Question | Judgment |
| --- | --- |
| Does the proof match the original problem? | Yes, through the direct cardinal-product, ordinary-integral, and infimum bridges. |
| Did the exact selected revision pass execution? | Yes, every check below exited zero with all source hashes preserved. |
| Is the full original scope represented? | Yes under the proposed exact-value-rule interpretation, with all positive node counts and the negative coefficient-one asymptotic result. |
| Does the formalization meet the checked completeness standard? | Yes under the standard Lean foundations recorded below. |

| Repeated check | Result | Evidence |
| --- | --- | --- |
| build | Passed, exit 0 | [build output](submission-logs/build.log) |
| challenge | Passed, exit 0 | [challenge output](submission-logs/challenge.log) |
| axioms | Passed, exit 0 | [axioms output](submission-logs/axioms.log) |
| standalone | Passed, exit 0 | [standalone output](submission-logs/standalone.log) |
| kernel | Passed, exit 0 | [kernel output](submission-logs/kernel.log) |

The repeated project build used the existing pinned dependency cache. The earlier fresh proof-source build and eight-target official-helper run are recorded in [the full verification report](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/d64aff236eb7e63a55e8ac91309150c4a12548b0/verification/report.md). The final source checks and replay independently revisit the selected revision. All 17 printed axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`. The complete proof dependency closure contains 58,042 declarations and was replayed into an initially empty environment.

The original problem page, its LaTeX text, the public discussion and proof-claim page, and related prize PRs were refreshed. The problem still states the same two questions. PR 5133 concerns sharp asymptotics and leaves exact finite minima open. The other located prize submissions have the scoped or mapping limitations recorded in the earlier report. The public discussion includes finite-case certificates and conditional asymptotic claims. These records establish the reviewed overlap and attribution. Absolute novelty and first priority remain unconfirmed.

The four equal contributors remain Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer. Ghuffy1 is owner and submitting account. The prior asymptotic proof retains seanm27lol's credit. AI assistance is acknowledged. The manuscript and all proof source files retain their reviewed contents.

The complete proof-dependency replay uses the pinned Lean kernel. An independently implemented checker was not run. The earlier additional whole-import replay was stopped, as documented in the full report. Mathematical and scope acceptance, personal attribution and identity, priority, and award eligibility remain for organizer review.

The owner has authorized publication of the necessary evidence and submission to The Justin Sun Prize following this check. The catalog contribution supplies the reviewed source, manuscript, attribution, and verification evidence for that review.
