# Reproducing the proof

## Pinned source and environment

The checked proof revision is recorded in `verification/VERIFIED_COMMIT`. The branch `main` contains that revision. Verification evidence is added in a later commit so that its report can cite the proof revision without a circular commit reference.

The development uses Lean `4.34.1`, whose release identifies commit `5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`. The complete dependency revisions are in `lake-manifest.json`.

Start with a fresh clone. Before checking out the proof revision, read it from the verification record.

```sh
git clone https://github.com/Ghuffy1/erdos-1131-exact-minimum.git
cd erdos-1131-exact-minimum
proof_revision=$(cat verification/VERIFIED_COMMIT)
git checkout "$proof_revision"
lake exe cache get
lake build
lake env lean Challenge.lean
lake env lean tools/AxiomAudit.lean
lake env lean --run tools/ReplayProof.lean
```

PowerShell users can read the revision with

```powershell
$proofRevision = Get-Content verification/VERIFIED_COMMIT
git checkout $proofRevision
```

Lake obtains the compiler named by `lean-toolchain` through Elan and uses the locked dependency manifest. The ordinary build includes the exact-minimum modules, the standalone exact-minimum file, the attributed asymptotic modules, and the combined source-correspondence challenge.

## What the checks establish

`Challenge.lean` defines the cardinal product directly as

```text
product over j != i of (t - x_j) / (x_i - x_j)
```

It then uses the ordinary integral on `[-1,1]` and the infimum over all distinct real nodes in that interval. The checked bridges identify these definitions with the construction and with the earlier asymptotic proof. The final theorem contains both the all-positive-node-count exact-minimum statement and the negative answer to the coefficient-one limit.

`tools/AxiomAudit.lean` prints every submission target and correspondence bridge with its transitive axiom dependencies. The expected logical foundations are `propext`, `Classical.choice`, and `Quot.sound`.

`tools/ReplayProof.lean` collects the full transitive dependency closure, includes mutual inductive declarations and constructors, rejects unsafe or partial proof dependencies, and replays the original declarations into an initially empty kernel environment. This is the kernel implementation shipped with Lean. The verification report records any additional checking methods actually completed.

## Mathematical attribution

The exact-minimum construction and its proof are in the paper and the `Erdos1131` modules. The prior coefficient-one disproof remains attributed to its original source. Compatibility adaptations and the equality of the two infima are recorded separately in [THIRD_PARTY.md](THIRD_PARTY.md).

The exact value rule is a finite mathematical construction with rapidly growing matrices. The formal definitions use classical choice. The repository supplies the mathematical proof and its formalization.
