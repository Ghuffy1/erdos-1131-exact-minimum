# Prior-art and related-submission record

This record supports the private preparation of JSP-000938, corresponding to Erdős Problem 1131. The search was refreshed on November 11, 2026. Absolute first priority remains unestablished.

## Original problem and established methods

The original problem asks for the minimum of the ordinary integral of the sum of squared Lagrange cardinal functions and, in particular, whether its deficit from two has leading coefficient one. The source page records the older interpolation literature and the known bounds. Its catalogue status and comments are evidence of what that page records at the retrieval date. [Original problem](https://www.erdosproblems.com/1131)

General real quantifier elimination already implies an effective algebraic description for each fixed finite-node optimization problem after clearing positive denominators. Hermite trace forms and parametric Hermite matrices are established methods. The proposed new contribution is the particular uniform rational construction, its explicit dimension and degree bounds, the root-selection rule, and its complete formal proof. The manuscript credits the underlying methods. [Manuscript bibliography](../paper/exact-minimum.pdf)

## Directly examined public sources

| Source | Observed scope and treatment |
| --- | --- |
| seanm27lol, original proof commit `31574acf09ae50430c08da92288800fe7d26c7fd` | A prior coefficient-one asymptotic disproof. Its complete source was retrieved, adapted with a recorded diff, and checked in the submitted environment. The prior contribution remains credited to its author. |
| Formal Conjectures PR 4585 | Its metadata, changed files, and available reviews identify the asymptotic contribution and leave the exact minimum open. The proposed statement does not supply the present all-node-count value construction. |
| Patrick White, exact four-node result, August 11, 2026 | An explicit global proof for four nodes and its algebraic minimum. The article records a finite-case contribution and explicitly limits its scope. Its endpoint-variation and Gram-matrix arguments overlap with preliminary methods used in the present paper and are credited. |
| Brutman–Toledano, 1997 | The cited publication studies the same extremal problem. Its complete body remained inaccessible through the attempted publisher endpoints. The current PR 5133 describes its numerical minima, extrapolation, and identities. Those descriptions have not been substituted for independent full-text examination. |
| January 2026 asymptotic preprint, DOI `10.20944/preprints202601.0875.v1` | A publicly indexed asymptotic claim. It is not a dependency of the submitted proof. Access to the full text was incomplete in this refresh, so no conclusion about its correctness or complete scope is based on this retrieval. |

The primary links are the [original asymptotic source](https://github.com/seanm27lol/erdos-1131-lean/tree/31574acf09ae50430c08da92288800fe7d26c7fd), [Formal Conjectures PR 4585](https://github.com/google-deepmind/formal-conjectures/pull/4585), [four-node article](https://erdosproblemaday.com/day/1131-exact-four-node-minimum), [1997 publication](https://doi.org/10.1016/S0898-1221(97)00232-0), and [2026 preprint](https://doi.org/10.20944/preprints202601.0875.v1).

The community's AI-contributions record also lists Liam Price and GPT-5.5 Pro on April 26, 2026, under pending assessment for partial progress on Problem 1131. That historical record is additional evidence of prior public activity. The present preparation attributes the integrated formal proof to its actual repository source and makes no claim to originate the earlier asymptotic disproof. [Pinned community record](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems/1f49e918b9d068e7a1ce8aa4a849a3a7df372b81)

## Prize submission search

The search used JSP-000938, Erdős 1131, Lagrange interpolation, and the relevant source repositories. It covered open, closed, and merged PR results. The four relevant prize PRs had their metadata, changed files, available reviews, and issue comments captured at approximately 16:56 UTC on November 11, 2026.

| Prize PR | Status at retrieval | Observed relationship |
| --- | --- | --- |
| 5133 | Open, unmerged | Kaiwen Jin's October 24, 2026 sharp-asymptotic paper is submitted as a publication-reference update. The PR expressly leaves exact finite minima open. Its claimed sharp result requires its own mathematical review. |
| 4514 | Closed, unmerged | A two-node or numerical Lagrange-integral claim. It does not provide the all-positive-node-count construction or the full original statement. |
| 3226 | Closed, unmerged | The body identifies Erdős 938 while addressing catalog JSP-000938. The current catalog maps JSP-000938 to Erdős 1131. This mapping conflict prevents treating it as evidence of a full proof of the present problem. |
| 2496 | Closed, unmerged | The body expressly describes a scoped component and numerical instances. It does not claim a full formalization of the original problem. |

The public records are [PR 5133](https://github.com/TheJustinSunPrize/awards/pull/5133), [PR 4514](https://github.com/TheJustinSunPrize/awards/pull/4514), [PR 3226](https://github.com/TheJustinSunPrize/awards/pull/3226), and [PR 2496](https://github.com/TheJustinSunPrize/awards/pull/2496).

## Search interpretation

No identical all-node-count rational matrix and root-selection construction was identified among the materials examined. This is a bounded search result. Inaccessible full texts, unindexed repositories, unpublished work, and later submissions can affect priority.

The team's repository was prepared privately. The selected Git commit and the private verification records document the version checked. Independently checkable public history tying that version to a priority date will depend on a later authorized release. Commit timestamps alone do not establish first priority under the prize rules. [Priority and review rules](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/award-process.md)

The submission therefore requests mathematical, scope, attribution, and formal verification review. It preserves prior credit and makes no absolute first-priority claim.
