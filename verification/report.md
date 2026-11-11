# Verification of Erdős Problem 1131

**Overall verdict — verification passed for the stated full-scope algebraic value rule at proof commit `85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473`.**

The checked source gives an attained exact value for every positive node count by a finite rational polynomial and signature construction. It also supplies the negative answer to the original coefficient-one asymptotic question through an explicitly credited prior proof. Both conclusions are proved for a direct transcription of the original cardinal-product integral. Acceptance of the proposed value rule as a resolution of the problem remains subject to the organizers' mathematical and scope review.

| Required question | Judgment | Evidence |
| --- | --- | --- |
| Does the statement address the specified original problem? | Yes | Direct product, interval, admissibility, and infimum definitions in `Challenge.lean`, with checked equality bridges |
| Did this exact commit pass the recorded checks? | Yes | Fresh proof-source build, all eight explicit helper targets, standalone recheck, axiom audit, and kernel replay |
| Is the original mathematical scope covered? | Yes under the exact algebraic value-rule interpretation | All positive node counts, attainment, universal lower bound, finite degree bound, and the negative coefficient-one result |
| Are the formal proofs complete under standard Lean foundations? | Yes for the checked targets | Exactly `propext`, `Classical.choice`, and `Quot.sound`, with complete dependency replay |

This is an AI-assisted pre-submission verification record. Independent human review, prize acceptance, identity verification, and priority certification remain external stages.

## Fixed sources

- The original proof repository is `https://github.com/Ghuffy1/erdos-1131-exact-minimum`, branch `main`. The selected proof revision is `85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473`. A fresh private GitHub clone was checked at that exact revision. The later evidence and submission commits preserve that selected revision.
- The applicable prize guidance is pinned to `b1bfe454d37db2838ef76756830aeb23c40de95e`. The catalog maps JSP-000938 to Erdős 1131. The problem is outside the listed MathDB pilot and uses the legacy contribution-PR route. No contribution PR has been opened for this preparation. [Prize guidance](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/CONTRIBUTING.md)
- The source formula is the ordinary integral of the sum of squared Lagrange cardinal functions over arbitrary distinct real nodes in the closed interval. The separate asymptotic question asks whether `n(2-m_n)` tends to one. The captured problem page and LaTeX page were retrieved on November 11, 2026. [Original problem](https://www.erdosproblems.com/1131)
- The exact-minimum manuscript is the nine-page November 11, 2026 version. Theorem 1.1 and Sections 2–7 contain the value construction and proof. Its SHA-256 is `ba51d5182e564c8539461eef5d77452c08feb966ebb673e033dcb74aa4bc5034`. [Manuscript](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/paper/exact-minimum.pdf)
- The asymptotic source is `seanm27lol/erdos-1131-lean` at `31574acf09ae50430c08da92288800fe7d26c7fd`. Its proof and exposition retain their original credit and Apache-2.0 license. The adaptation record identifies every changed file. [Prior source](https://github.com/seanm27lol/erdos-1131-lean/tree/31574acf09ae50430c08da92288800fe7d26c7fd)

## Original statement and correspondence

For distinct real nodes `x_1,...,x_n` in `[-1,1]`, the cardinal function is the product of `(t-x_j)/(x_i-x_j)` over `j != i`. The minimum concerns the ordinary integral of the sum of the squares of these functions. Distinctness guarantees nonzero denominators. The empty product for one node gives the value two. The original asymptotic expression is equivalent to `n(2-m_n) -> 1`.

`OriginalProblem1131.admissible`, `cardinal`, `integral`, and `infimum` directly express these objects. The checked bridges `admissible_eq`, `integral_eq`, and `infimum_eq` identify them with the proof's definitions. Permutations of arbitrary admissible nodes are allowed. The proof's ordered and endpoint reductions are internal lemmas. [Direct transcription](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/Challenge.lean)

The exact conclusion has the following form.

```text
For every n > 0 there exist admissible nodes whose integral equals
algebraicMinimum n. This value bounds the integral of every admissible
configuration from below. Also, n * (2 - infimum n) does not tend to 1.
```

For `n >= 2`, put `k=n-1`, `d=2n(n-1)`, and `M=(d+1)^k`. A rational symmetric polynomial matrix of order `M` produces a nonzero rational boundary polynomial of degree at most `kdM`. Order its real roots in `(0,2)`, take rational samples between successive roots and the endpoint two, and count the samples with signature one. The corresponding next root is the minimum. `algebraicMinimum_eq_minimum` proves equality with the infimum. The proof of this equality uses the infimum to identify the selected root. The value definition uses the polynomial, roots, rational samples, and signatures. [Value rule](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/RootSelection.lean)

| Original obligation | Checked declarations and scope |
| --- | --- |
| Ordinary integral and arbitrary distinct nodes in `[-1,1]` | `OriginalProblem1131.integral_eq`, `admissible_eq`, and `infimum_eq` |
| Every positive node count, including one | `Erdos1131.erdos1131_solution`, `algebraicMinimum_eq_minimum`, and `minimum_one` |
| Attainment and universal minimality | `Erdos1131.minimum_attained` and the universal lower-bound clause of `erdos1131_solution` |
| A finite rational value construction | `boundaryPolynomial_ne_zero`, `boundaryPolynomial_degree`, and the signature-based root selection |
| Same functional in the prior asymptotic proof | `energy_eq_reference_functional`, `attainable_values_eq_reference`, and `minimum_eq_reference` |
| Original, unshifted asymptotic question | `asymptotic_coefficient_one_false` and `OriginalProblem1131.asymptotic_original` |
| Both requested conclusions together | `OriginalProblem1131.full_original_problem` |

The formal definitions use classical choice. The construction specifies a finite mathematical rule and explicit sizes. Practical evaluation of the rapidly growing matrices was outside this verification. A sharp asymptotic coefficient and classification of every minimizing configuration are outside the claims of the combined theorem.

## Actual execution

The operating system was `Windows-10-10.0.19045-SP0` on `AMD64`. Lean was `4.34.1`, release commit `5045d0056413266e57c625dcd7c365b10e377c52`. Lake was `5.0.0-src+5045d00`. The checked executable hashes and all nine dependency revisions are recorded in [environment.json](environment.json).

The build used a new clone of the private original repository, a pinned compiler path, and a controlled environment with compiler-path overrides and credential environment variables cleared. All temporary files and caches were on the project drive. Dependencies came from a reused task-local cache with the nine locked Git revisions and clean tracked sources checked. The proof sources were freshly built. No container or virtual-machine boundary was used.

| Command | Exit | Elapsed seconds | Complete output |
| --- | --- | --- | --- |
| `lake build` | 0 | 805.7 | [build](logs/build.log) |
| `lake env lean Challenge.lean` | 0 | 25.2 | [challenge](logs/challenge.log) |
| `lake env lean tools/AxiomAudit.lean` | 0 | 25.7 | [axioms](logs/axioms.log) |
| `lake env lean Erdos1131Full.lean` | 0 | 87.3 | [standalone](logs/standalone.log) |
| `lake env lean --run tools/ReplayProof.lean` | 0 | 272.1 | [kernel](logs/kernel.log) |

All 92 tracked files were byte-identical before and after each stage. Source hashes are independently anchored by `provenance/source-sha256.json` at the selected commit. The build emitted style and deprecation warnings. Its final exit status was zero.

The manuscript's author order, email mapping, nine-page length, stored hash, and AI acknowledgment were checked. `CITATION.cff` passed the official version 1.2.0 JSON schema. The source metadata and license references were checked for consistency. [Metadata checks](metadata-checks.json)

The official helper at the pinned prize revision ran three checks for each of eight targets, comprising an explicit module build, source re-elaboration, and generated axiom check. All 24 target commands exited zero. The helper reported `standard_axioms_only`, stable inputs, and eight completed target records. This mechanical status is accompanied by the separate statement and coverage assessment above.

The first helper attempt and first whole-import checker attempt were interrupted before an exit code was observed. Their processes were absent after a client context update. Their partial outputs were preserved privately. The helper was repeated successfully in a new log location. The previously completed source build, direct target checks, and proof-dependency replay were preserved.

| Explicit helper target | Result | Transitive axioms |
| --- | --- | --- |
| `Erdos1131.erdos1131_solution` | Passed | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1131.minimum_attained` | Passed | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1131.boundaryPolynomial_degree` | Passed | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1131Submission.minimum_eq_reference` | Passed | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1131Submission.asymptotic_coefficient_one_false` | Passed | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1131Submission.complete_problem` | Passed | `propext`, `Classical.choice`, `Quot.sound` |
| `OriginalProblem1131.integral_eq` | Passed | `propext`, `Classical.choice`, `Quot.sound` |
| `OriginalProblem1131.full_original_problem` | Passed | `propext`, `Classical.choice`, `Quot.sound` |

`tools/AxiomAudit.lean` additionally prints 17 target and bridge axiom lists, including the prior asymptotic theorem and all original-definition equalities. Each list contains exactly the same three standard foundations. The complete declaration types and outputs are preserved in [the axiom log](logs/axioms.log).

## Kernel replay and trust

`tools/ReplayProof.lean` collected **58,042 declarations** in the complete dependency closure of the combined result, exact-value equality, attainment, and degree bound. The collection includes mutual inductive declarations, constructors, recursors, and quotient support. It rejected unsafe or partial proof dependencies and any axiom outside the three listed foundations. The original declarations were then replayed into an initially empty kernel environment, and all five roots were found in the resulting environment. The replay completed successfully. [Replay output](logs/kernel.log)

The additional shipped `leanchecker --fresh --verbose Challenge` attempt covers every imported declaration, including unused library material. Its initial run was interrupted by the client context update. The retry was intentionally stopped after the complete target-dependency replay and all explicit target checks had passed. Its observed exit code was `4294967295` and all source hashes were unchanged. A completed whole-import replay is outside the verification claims of this report.

The completed proof-dependency replay uses the kernel implementation shipped with the pinned Lean release. No independently implemented kernel checker was run. Reused compiled dependencies and the compiler remain part of the environment's trust boundary, while the replay checks all 58,042 declarations in the selected proof closure. The replay driver's import API uses an unsafe entry point outside that closure. Container isolation and the entire optional verification workflow's security guarantees are outside the claims of this report.

## Attribution and prior art

Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer are listed in surname order and declared equal contributors to the new exact-minimum work and its integration. Ghuffy1 is the repository owner and submitting account. This records the user's attribution declaration. It does not independently establish each person's identity or historical contribution. [Author record](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/AUTHORS.md)

The prior coefficient-one disproof and original asymptotic formalization remain attributed to seanm27lol. The new contribution claimed by the team is the exact finite-degree construction and its proof. The manuscript credits classical real algebraic algorithms and Hermite trace methods. General quantifier elimination already implies an effective algebraic description of such minima. [Prior sources and adaptation details](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/THIRD_PARTY.md)

The related-submission search covered the prize's open, merged, and closed PR metadata and available discussion, the original problem page, the prior proof repository, and the referenced publications. Existing prize PR 5133 concerns sharp asymptotics and explicitly leaves exact finite minima open. PRs 4514, 3226, and 2496 were also checked for finite-scope and mapping differences. The complete 1997 Brutman–Toledano article remained inaccessible during this audit. The documented overlap and credit decisions follow this bounded search. Absolute first priority remains unestablished. [Detailed search record](prior-art.md)

## Evidence and reproduction

The portable [target manifest](targets.json) uses `/work/erdos-1131-exact-minimum` as an example checkout root. Set that field to the local absolute checkout path before running the official helper. Only the root path differs from the executed target manifest, whose SHA-256 is `7b31ebbe09fc3abe0d3d441587e5066304ae9e6a1f108cbc7ed63b35302d1765`. Semantic coverage was entered by the reviewer, then checked mechanically with the pinned source targets.

[results.json](results.json) records the actual stage times, helper outputs, log hashes, and verification limits. Published log copies preserve the compiler output, with local working-directory prefixes replaced by `/work`. Original local receipts and captured source pages remain in the private preparation records. No diagnostic edits were applied to the checked proof commit. [Reproduction instructions](https://github.com/Ghuffy1/erdos-1131-exact-minimum/blob/85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473/REPRODUCING.md)

## External stages

The repository remains private. The submission packet is prepared for later release. The organizers must review the mathematical interpretation, formal proof, attribution, competing submissions, and priority. Each potential recipient must complete the applicable personal claim, identity, public-review, and written-confirmation steps. These outcomes are outside the formal verification verdict.
