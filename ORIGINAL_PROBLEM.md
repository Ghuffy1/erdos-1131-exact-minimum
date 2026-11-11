# Original problem and scope

The source is [Erdős Problem 1131](https://www.erdosproblems.com/1131), corresponding to [JSP-000938](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/problems/catalog-0901-1000.md#JSP-000938).

For each positive integer `n`, choose arbitrary distinct real nodes `x₁, …, xₙ` in the closed interval `[-1,1]`. The cardinal function at `xᵢ` is the product, over `j ≠ i`, of `(t - xⱼ)/(xᵢ - xⱼ)`. The objective is the ordinary Lebesgue integral on `[-1,1]` of the sum of their squares. Let `mₙ` be its infimum.

The source asks for this minimum and asks whether `n(2 - mₙ)` tends to `1`. The catalog's abbreviated title is interpreted through this original formula.

## Exact-minimum result

The paper's Theorem 1.1 gives an attained minimum for every positive `n` and specifies its value by a finite rational polynomial and a real-root selection rule. It includes arbitrary node order, endpoint cases, and collision handling within the polynomial encoding. `Erdos1131.erdos1131_solution` proves attainment, equality with the selected algebraic value, and the lower bound for every admissible configuration.

## Asymptotic question

The coefficient-one limit is false. The earlier proof by `seanm27lol` constructs explicit admissible Chebyshev comparison nodes with an eventual scaled deficit at least `106/105`. The version included here is adapted from its pinned source with the original credit and Apache-2.0 license retained.

`Erdos1131Submission.minimum_eq_reference` identifies the two infima. The shift from the earlier proof's index `N+1` to the original index `n` is handled in `Erdos1131Submission.asymptotic_coefficient_one_false`.

## Independent statement check

`Challenge.lean` writes the original product, interval integral, and infimum directly. The final declaration `OriginalProblem1131.full_original_problem` combines the exact-minimum conclusion with the negative answer to the asymptotic question under these definitions.

The constructive minimum uses classical mathematical definitions. The implementation of the finite value rule follows the proof's quotient and trace construction, with all sizes and degree bounds specified in the paper.
