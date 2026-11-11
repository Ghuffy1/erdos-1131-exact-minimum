# Exact algebraic minima for Erdős Problem 1131

This repository contains an explicit algebraic construction of the minimum ordinary integral of the sum of squared Lagrange cardinal functions, for every positive number of distinct real nodes in `[-1,1]`. The minimum is attained. The construction uses a rational Hermite matrix, a univariate polynomial, and an exact root-selection rule.

The original question also asks about the coefficient-one asymptotic. The repository includes the previously published disproof by `seanm27lol`, with its original attribution and license, together with proved bridges identifying the two formulations of the interpolation functional. The combined target addresses both questions.

## Authors and ownership

| Author | GitHub account | Contribution |
| --- | --- | --- |
| Will Howe | [H0W4RD-dev](https://github.com/H0W4RD-dev) | Equal contribution to the new exact-minimum work |
| Grant Huffman | [Ghuffy1](https://github.com/Ghuffy1) | Equal contribution to the new exact-minimum work, repository owner and submitting contact |
| Jensen Kohlmeyer | [JENW1N](https://github.com/JENW1N) | Equal contribution to the new exact-minimum work |
| Liam Kruer | [lkruer](https://github.com/lkruer) | Equal contribution to the new exact-minimum work |

The authors are listed in alphabetical order by surname. The team declares equal contributions. [AUTHORS.md](AUTHORS.md) records the attribution and AI acknowledgment. [THIRD_PARTY.md](THIRD_PARTY.md) identifies the earlier asymptotic proof and all adaptations.

## Mathematical paper

[An exact algebraic construction for Erdős's interpolation minimum](paper/exact-minimum.pdf) gives the complete mathematical proof of the exact-minimum construction. The corresponding source is [paper/exact-minimum.tex](paper/exact-minimum.tex). The prior asymptotic argument is preserved in [references/seanm27lol-asymptotic-proof.md](references/seanm27lol-asymptotic-proof.md).

For `n ≥ 2`, let `k = n - 1` and `d = 2n(n - 1)`. The rational symmetric matrix has order `(d + 1)^k`. A nonzero coefficient of its characteristic polynomial has degree at most `k d (d + 1)^k`. Ordered real roots in `(0,2)`, together with signatures at rational points between them, specify the minimum exactly. These matrices grow rapidly with `n`. The mathematical definitions in the formal proof use classical choice.

## Main declarations

| Declaration | Content |
| --- | --- |
| `Erdos1131.erdos1131_solution` | All-positive-`n` exact minimum, attainment, and universal lower bound |
| `Erdos1131.algebraicMinimum_eq_minimum` | The explicit value rule equals the original infimum |
| `Erdos1131.minimum_attained` | An admissible minimizer exists |
| `Erdos1131.boundaryPolynomial_degree` | Degree bound for the boundary polynomial |
| `Erdos1131Submission.minimum_eq_reference` | Equality with the infimum used by the prior asymptotic proof |
| `Erdos1131Submission.asymptotic_coefficient_one_false` | The original, unshifted coefficient-one limit is false |
| `Erdos1131Submission.complete_problem` | Combined exact-minimum and asymptotic conclusions |
| `OriginalProblem1131.full_original_problem` | The combined result for independently written product and integral definitions |

[Submission.lean](Submission.lean) assembles the results. [Challenge.lean](Challenge.lean) writes the cardinal product and integral directly from the original question and proves their correspondence with the submitted definitions. [Erdos1131Full.lean](Erdos1131Full.lean) is a single-file version of the exact-minimum proof. The modular construction is retained alongside it.

## Reproduction

The project pins Lean `4.34.1` and mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. All dependency revisions are recorded in [lake-manifest.json](lake-manifest.json).

From a fresh checkout with Elan installed, run

```sh
lake exe cache get
lake build
lake env lean Challenge.lean
lake env lean tools/AxiomAudit.lean
lake env lean --run tools/ReplayProof.lean
```

The last command replays the target theorems and their complete dependency closure into an initially empty Lean kernel environment. It uses the kernel implementation shipped with the pinned toolchain.

[REPRODUCING.md](REPRODUCING.md) describes the version and trust checks. The verification records identify the exact checked commit and actual results.

## Submission context

The proposed submission concerns [JSP-000938](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/problems/catalog-0901-1000.md#JSP-000938), corresponding to [Erdős Problem 1131](https://www.erdosproblems.com/1131). Mathematical acceptance, authorship verification, priority, and award eligibility are determined through the prize's review process. The manuscript credits the classical algebraic methods and earlier interpolation work on which the construction draws.

## License

The prepared repository uses [Apache-2.0](LICENSE). Existing third-party attribution is retained in [NOTICE](NOTICE), [THIRD_PARTY.md](THIRD_PARTY.md), and the source headers.
