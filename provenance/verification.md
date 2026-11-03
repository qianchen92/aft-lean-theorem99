# Verified standalone snapshot (2026-11-04)

The upstream Lean directory at commit
`176d128e3361f975a3c7e2f889fdc5f2c96c1d29` passed its existing
`./check-current.sh`, including the 49-file manuscript snapshot comparison.
The standalone repository contains the exact 1805 local Lean modules in the
transitive import closure of its current proof entry. Their SHA-256 hashes
are verified by `scripts/verify-snapshot.py` on every check.

The added root statement was checked separately, then `./check.sh` exited 0:

- `lake build CurrentAFT Theorem99`: successful (9842 build jobs).
- `lake env lean Audit.lean`: 3 root declarations, 20671 CurrentAFT declarations,
  and 17948 reused AFT declarations passed transitive axiom collection.
- Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. An imported
  `sorryAx` or custom axiom makes the audit fail.
- Working-tree and staged diff whitespace checks passed.

Existing upstream linter warnings and legacy whitespace are retained byte-for-byte.
Diff checks apply to changes relative to the imported snapshot. The new root module compiled
without warnings. Builds reused local compilation caches; those caches and
all manuscript files are excluded from Git. Dependencies and toolchain are
locked, and a new clone can obtain dependency caches with `lake exe cache get`.

The root statement explicitly uses a single static metadata witness and a
single actual sampler in every conclusion. The neighboring evaluator theorem
is quantified over arbitrary encoded affine data and integer inputs. A manual
comparison checked the paper's `thm:df-constructive-aft`, `def:gaussian-t-aft`,
and `def:t-aft` against these statements. This comparison is a specification
review; the axiom audit alone does not establish correspondence with prose.

Complexity is formalized in the concrete counted binary-operation model.
No additional simulation theorem into a standard probabilistic Turing machine
is included or claimed. File fingerprints and counts are in `verification.json`.
