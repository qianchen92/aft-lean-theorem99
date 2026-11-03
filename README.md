# Theorem 9.9: Gaussian AFT in Lean

This is a standalone Lean proof snapshot for Theorem 9.9 of the Learning with Algebraic Rounding paper, using an explicit counted binary-operation model. Start with **[Theorem99.lean](Theorem99.lean)**: its `theorem_9_9` statement collects the main quantifiers and guarantees in one place.

The repository contains proof sources and locked dependency specifications. It does not include the manuscript or generated build artifacts.

## Where to start

- **[`theorem_9_9`](Theorem99.lean)**: for each fixed accuracy order, one set of finite program data, independent of the security parameter, supplies polynomial fair-bit tape length and worst-case work, integral affine outputs and modular invertibility on every tape, the actual output law, eventual inverse-polynomial accuracy, and the paper's quantitative error bound. The statement also includes negligible remainders and exact uniformity and independence of the transformed public matrix.
- **[`evaluator_correct_and_polynomial`](Theorem99.lean)**: correctness and polynomial cost of the deterministic affine evaluator on arbitrary integer matrix, offset, and input encodings of the appropriate shape. Its cost is polynomial in the security parameter plus the actual encoding lengths.
- [ActualConstructiveSampler.lean](CurrentAFT/ActualConstructiveSampler.lean): the underlying constructive existence, accuracy, and quantitative error theorems.
- [ActualConstructiveProgram.lean](CurrentAFT/ActualConstructiveProgram.lean): the actual program and its connections to calibration-table generation and the source-independent public experiment.
- [ActualAffineEvaluator.lean](CurrentAFT/ActualAffineEvaluator.lean): the independent deterministic evaluator.

The accuracy order is fixed before the program data and polynomial budgets are chosen. The same public parameter family then applies at every security parameter. The result does not require a single algorithm that takes the accuracy order as input and is uniformly efficient across all orders.

## Notation

| Paper concept | Lean definition |
| --- | --- |
| Security parameter and accuracy order | `security`, `accuracyOrder` |
| Calibration order, D = 4a + 267 | `CurrentAFT.Parameters.calibrationOrder accuracyOrder` |
| Base, modulus q, and total dimension | `Parameters.base`, `Parameters.modulus`, `Parameters.dimension` |
| Actual fair-bit sampling program | `ActualConstructiveSampler.run` |
| Integer matrix and offset | `CurrentBinaryAffineEmitter.matrix`, `CurrentBinaryAffineEmitter.offset` |
| Output law on an independent Gaussian source | `ActualConstructiveSampler.law`, connected to the executed program by `law_eq` |
| Uniform law on the fixed label map's actual zero fiber | `CurrentZeroFiber.uniformFiber` |
| Numerical implementation error | `ActualConstructiveSampler.numericalError` |
| Negligible analytical remainder | `ActualGaussianRemainder.remainder` |

Omitted namespace prefixes in this table are `CurrentAFT`. The definitions imported by the root file determine the precise meaning of each name.

## Reproduce the checks

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
./check.sh
```

Use the committed `lean-toolchain` and `lake-manifest.json`; do not run `lake update` first. The toolchain is pinned to Lean `v4.29.0-rc1`, and mathlib is pinned to commit `33a7291a345d718bca41f8ae8a9bae365d8f2a3e`. The executable checks and axiom-audit rules are defined in `check.sh` and the audit source.

See the [initial verification record](provenance/verification.md) for the original snapshot, and the [cleanup verification record](provenance/cleanup-2026-11-04.md) for the pruned source inventory and subsequent checks.

## Scope of the complexity guarantee

`work` counts explicit Boolean/list/counter operations on binary data, accounting for array reads and writes, random-tape decoding, and intermediate operand sizes. The root theorem proves polynomial worst-case cost in this model. **This snapshot does not formalize a general simulation of that model by a standard probabilistic Turing machine**, and therefore does not claim that such a simulation has been verified in Lean.

Lean checks proofs of the encoded statements. Assessing their correspondence with the paper still requires reading the root theorem and its referenced definitions. The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Provenance and source inventory

The upstream manuscript repository commit is `176d128e3361f975a3c7e2f889fdc5f2c96c1d29`. Retained upstream proof modules are unchanged byte for byte. The root theorem and standalone verification files provide navigation and reproducibility for this repository.

The repository retains exactly the local dependency closure needed by `Theorem99.lean` and the audit: 1794 Lean files. Modules with historical version names remain when the current proof actually depends on them; version markers in filenames alone do not indicate that a module is unused.

The original module snapshot is recorded in [upstream-lean-snapshot.json](provenance/upstream-lean-snapshot.json), and the manuscript alignment record is in [upstream-manuscript-manifest.json](provenance/upstream-manuscript-manifest.json). This repository contains the proof snapshot, without the manuscript's LaTeX, PDF, local `.lake` caches, or upstream Git history. The first build creates `.lake` locally.

Dependency cleanup removed 13 modules unused by the root theorem. Their paths and original hashes are listed in [pruned-modules.json](provenance/pruned-modules.json). `check.sh` verifies retained source hashes, the explicit deletion inventory, and dependency reachability. Missing dependencies or additional unreachable local Lean modules cause the checks to fail.
