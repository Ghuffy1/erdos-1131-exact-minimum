# Third-party sources and adaptations

## Previously published asymptotic disproof

The files under `Erdos1131Asymptotic/` are adapted from the original repository [seanm27lol/erdos-1131-lean](https://github.com/seanm27lol/erdos-1131-lean/tree/31574acf09ae50430c08da92288800fe7d26c7fd), at the immutable commit

```text
31574acf09ae50430c08da92288800fe7d26c7fd
```

That source proves an eventual scaled deficit of at least `106/105`, which disproves the coefficient-one limit. Its mathematical result and original formalization retain their upstream credit. The original source uses Lean `4.28.0` and mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

The prepared version uses this repository's Lean `4.34.1` environment. Module and namespace prefixes change from `Erdos1131` to `Erdos1131Asymptotic`. Compatibility changes are recorded against the pinned originals in `provenance/asymptotic-adaptations.diff` and `provenance/asymptotic-sources.json`. The new correspondence and integration arguments are in [Submission.lean](Submission.lean).

The upstream work is licensed under Apache-2.0. Its license is preserved as the repository [LICENSE](LICENSE). The original mathematical exposition is included as [references/seanm27lol-asymptotic-proof.md](references/seanm27lol-asymptotic-proof.md).

## Mathematical prior work

The paper's bibliography credits Basu, Pollack, and Roy for general real algebraic algorithms, Le and Safey El Din for parametric Hermite-matrix methods, Erdős, Szabados, Varma, and Vértesi for the interpolation problem, Brutman and Toledano for the earlier numerical study, and Patrick White for the four-node analysis. The construction specializes classical ideas to an explicit fixed-basis value rule.

## Mathlib and Lean

The formalization uses Lean and mathlib through the revisions in `lean-toolchain` and `lake-manifest.json`. Their contributors retain their respective copyrights and licenses. The dependency source and build caches are fetched through Lake.

## Prize guidance

The submission preparation uses the prize guidance at [TheJustinSunPrize/awards, commit b1bfe454d37db2838ef76756830aeb23c40de95e](https://github.com/TheJustinSunPrize/awards/tree/b1bfe454d37db2838ef76756830aeb23c40de95e). Any adapted submission-template prose retains credit to The Justin Sun Prize contributors under that repository's content license.
