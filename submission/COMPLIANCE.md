# Submission readiness review

The materials are prepared against The Justin Sun Prize rules at `b1bfe454d37db2838ef76756830aeb23c40de95e`. This review concerns preparation of the common contribution submission. The repository remains private until the owner authorizes release.

## Contribution packet

| Requirement | Prepared evidence and result |
| --- | --- |
| Correct problem and current route | JSP-000938 maps to Erdős 1131. It is outside the 50-problem MathDB pilot at the pinned rules revision. The legacy contribution-PR route applies. |
| Complete mathematical solution and evidence | The nine-page exact-minimum paper and the credited prior asymptotic exposition cover the two original questions. The proposed all-node-count value rule is submitted for organizer scope and mathematical review. |
| Original proof repository under the submitter | `Ghuffy1/erdos-1131-exact-minimum` is privately owned by Ghuffy1. The complete new exact-minimum proof is integrated with clearly identified prior work. |
| Branch and full revision | `main` contains proof commit `85bd4c4dc7c99de780b7fc7e4a657d0e2b60c473`. The verification record concerns exactly that revision. |
| Exact target and source location | `OriginalProblem1131.full_original_problem` in `Challenge.lean`, with source and integration entries identified in the draft PR. |
| Original-statement correspondence | Direct product and integral definitions, arbitrary distinct nodes in the closed interval, all positive node counts, and the original asymptotic sequence are checked through explicit bridges. |
| Complete proof and dependencies | Fresh source build, eight explicit helper targets, the axiom audit, and kernel replay passed. The checked foundations are `propext`, `Classical.choice`, and `Quot.sound`. |
| Reproducibility | Lean 4.34.1, exact mathlib revision, all nine locked dependencies, reproduction commands, source hashes, and actual output are recorded. |
| Mathematical and formal attribution | Four equal new-work contributors are listed in surname order. Ghuffy1 is the owner and submitting contact. The prior asymptotic contribution retains its original author and license. |
| AI acknowledgment | Included in the paper and author records. |
| Supported award-repository changes | `catalog.patch` changes only the relevant entry's current-status description, proof information, attribution basis, and publication details. Its applicability was tested against the pinned prize checkout. |
| Consistent status and eligibility | The proposed entry keeps Open, Lean No, and eligibility No pending organizer review. The current index requires no change at this preparation stage. |
| Reference-only award submission | Proof code, manuscript, and verification evidence stay in the external original repository. The draft award PR contains the catalog patch and references. |
| Related-submission search | Open, closed, and merged search results were reviewed. PRs 5133, 4514, 3226, and 2496 and Formal Conjectures PR 4585 are discussed in the verification evidence. |
| Privacy review | Tracked content and commit history were checked for credentials, machine-private paths, identity documents, private payment details, and build caches. The public-facing evidence was prepared separately from private claim planning. |
| Licensing | Apache-2.0 covers the prepared proof repository, with upstream credits retained. Template-derived submission text is credited to The Justin Sun Prize contributors under CC BY 4.0. |

The full verification record is at [the evidence revision](https://github.com/Ghuffy1/erdos-1131-exact-minimum/tree/d64aff236eb7e63a55e8ac91309150c4a12548b0/verification). [Pinned contribution requirements](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/CONTRIBUTING.md)

## Stages that follow authorized release

| Stage | Responsible party and required outcome |
| --- | --- |
| Public availability and contribution PR | The owner authorizes release, rechecks current rules and competing submissions, and opens the contribution PR with these materials. |
| Mathematical and scope review | The organizers assess the proposed exact-value interpretation, correctness, and full original scope. |
| Formal proof and attribution review | The organizers reproduce the selected proof and assess the individual contribution evidence. A self-check report supports that review. |
| Personal claims | Each actual contributor uses their own account after the applicable merged-PR prerequisite. Ghuffy1's common submission does not make personal claims for the other authors. |
| Co-contributor source arrangement | The present repository is a personal repository owned by Ghuffy1. The other three authors should obtain organizer confirmation of the original-source and contribution-evidence arrangement for any personal Lean claim. Their equal authorship declaration remains recorded. |
| Identity verification | Each applicant sends the required identity email through the official process and establishes the account-to-author connection by a method accepted by the organizers. |
| Public review | Each contribution type has a 14-day period starting when the organizers publish its candidate entry. |
| Recipient confirmation | Written confirmation and resolution of relevant challenges precede an award. Payment and delivery information use the private official email channel. |
| Priority | The organizers assess selected revisions, prior sources, and independently checkable public history. The private preparation makes no absolute first-priority claim. |

The applicable follow-up rules are in the [award process](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/award-process.md) and [attribution guidance](https://github.com/TheJustinSunPrize/awards/blob/b1bfe454d37db2838ef76756830aeb23c40de95e/docs/attribution.md).

The submission text follows the prize contributors' published template and guidance, with problem-specific adaptations, under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
