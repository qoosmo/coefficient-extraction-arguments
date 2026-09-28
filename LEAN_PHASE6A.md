# Lean Phase 6A — committed Hadamard algebraic interface

This phase formalizes the deterministic algebraic core of Section 9.

It adds:

- geometric scaling of a table by `γ^i`;
- `Q_γ(X)` as the table polynomial of the scaled table;
- proof that this polynomial evaluates as `V_a(γX)`;
- the weighted bilinear sum `Σ γ^i a_i b_i`;
- the weighted middle-coefficient identity;
- the identity `Σ γ^i c_i = V_c(γ)`;
- geometric compression of a true Hadamard relation `a ∘ b = c`;
- the compressed coefficient relation;
- canonical low/high split witnesses;
- the compressed Hadamard opening identity.

This phase deliberately stops before DEEP quotient consistency, random-root
soundness, correlated agreement, and FRI/proximity soundness.
