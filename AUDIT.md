# Manuscript audit - 27 September 2026

This audit was performed after completion of Sections 1--21 and before the Lean/Rust phase.

## Mechanical checks

- Full LaTeX/Biber build succeeds.
- No unresolved citations or cross-references.
- No duplicate labels.
- Every internal theorem/lemma/proposition/corollary has an explicit proof after this audit. The two intentionally unproved theorem statements are external inputs: Reed--Solomon correlated agreement and the Chiesa--Di--Hu--Zheng QROM compiler.
- The only remaining TeX box warnings are minor typography warnings; no content is clipped in the rendered PDF.

## Substantive consistency corrections

1. **Sparse matrix-vector reduction.** The Introduction previously described an earlier sorting/permutation aggregation idea. Section 13 ultimately uses a different and cleaner construction: two indexed selections, one Hadamard product, one committed inner product, and one public geometric linear functional. The Introduction and contribution list now match the proved protocol.
2. **Post-quantum scope.** The abstract and Introduction now state the actual theorem: relaxed round-by-round decoding knowledge plus the salted BCS IOR compiler gives QROM straight-line knowledge soundness. The manuscript does not say that Sumcheck itself needs to be made post-quantum, and it does not claim zero knowledge.
3. **Implementation status.** Claims implying that Lean/Rust results already exist were removed. The manuscript now treats formalization and controlled benchmarks as the next project phase.
4. **Missing internal proof.** The backend-sharing corollary in Section 18 now contains an explicit proof.

## Bibliography and freshness audit

- Corrected Twist and Shout to the final CRYPTO 2026 publication (Srinath Setty, Justin Thaler, Michael Zhu), while noting the earlier ePrint 2025/105 version.
- Added current 2026 comparison points:
  - BinarySpartan (ePrint 2026/1656),
  - Celer (CRYPTO 2026),
  - TensorSwitch (CRYPTO 2026),
  - Neo and SuperNeo (CRYPTO 2026).
- Removed an unused Chiesa--Manohar--Spooner bibliography entry.

## Claims intentionally retained as limitations

- Unique-decoding rather than list-decoding analysis.
- No zero-knowledge theorem.
- No claim that the coefficient-extraction prover is faster or smaller than optimized Sumcheck systems before controlled Rust measurements.
- QROM security is tied to the exact salted-BCS transcript/compiler model stated in Section 17.
- Characteristic and domain assumptions used by indexed tags, virtual reversal, and the current RS backend remain explicit.

## Next engineering phase

1. Freeze theorem signatures and create the Lean dependency skeleton.
2. Formalize Sections 3--10 first (table encoding through heterogeneous batching).
3. Extend Lean to lookup, permutation, sparse matvec, R1CS, and memory.
4. Implement the common Rust RS/FRI backend and primitive protocols.
5. Run controlled Sumcheck-vs-coefficient-extraction benchmarks under identical fields, hashes, security parameters, and hardware.
