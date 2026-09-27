# Coefficient-Extraction Arguments

Research repository for the paper **Coefficient-Extraction Arguments for Transparent Post-Quantum Proof Systems**.

The project develops a self-contained coefficient-extraction framework for table-form multilinear evaluation, committed inner products, Hadamard relations, logarithmic-derivative lookup and multiset checks, sparse matrix-vector products, and R1CS, with Reed-Solomon/FRI proximity as the transparent backend.

## Manuscript progress

Completed manuscript sections:

1. Introduction
2. Preliminaries and notation
3. Table-form Kronecker encoding
4. Coefficient-extraction calculus
5. Virtual Reed--Solomon words
6. Folding backend and generic coefficient-extraction protocol
7. Multilinear evaluation and public linear functionals
8. Committed inner products
9. Committed Hadamard relations
10. One folding test for heterogeneous relations
11. Logarithmic-derivative lookup arguments
12. Multiset and permutation arguments
13. Sparse matrix--vector products
14. Sparse R1CS
15. Memory consistency
16. Global soundness and decoding knowledge
17. Non-interactive post-quantum compilation
18. Complexity and concrete protocol costs
19. Comparison with existing proof-system architectures
20. Limitations, open problems, and research agenda
21. Conclusion

## Status

- Paper: Sections 1--21 drafted, audited, cross-reference checked, bibliography refreshed through September 2026, and compiled. The abstract/introduction have been reconciled with the final theorem set.
- Lean 4: Phase 1 algebraic kernel added (table coefficients, reversal, middle-coefficient/inner-product identity, and coefficient-form universal split); CI is configured to reject `sorry`, `admit`, and unapproved axioms.
- Rust: scaffold only; implementation and controlled benchmarks follow after the Lean theorem interface is fixed.

## Build the paper

```bash
./scripts/build-paper.sh
```

The PDF is written to `paper/main.pdf`.

## Repository layout

- `paper/` - LaTeX manuscript.
- `lean/` - Lean 4 formalization, mirroring the mathematical section structure.
- `rust/` - Rust reference implementation and benchmark kernels.
- `baselines/` - reproducible Sumcheck/PCS baselines used for controlled comparisons.
- `benchmarks/` - raw data, processing scripts, and generated tables.
- `scripts/` - build and validation entry points.

## Reproducibility rule

Primary performance claims will compare implementations under the same field, security parameters, hash/Merkle layout, hardware, compiler settings, and measurement procedure. Published external numbers are reported separately and are never mixed with same-machine measurements.

## GitHub bootstrap

After cloning/extracting this directory locally and authenticating `gh`:

```bash
./scripts/bootstrap-github.sh
```

The default target is `qoosmo/coefficient-extraction-arguments`; edit the script or pass a different repository name if needed.
