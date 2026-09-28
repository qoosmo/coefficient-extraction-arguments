# Lean Phase 6B — DEEP quotient algebraic interface

This phase formalizes the deterministic DEEP layer used in the Hadamard
protocol.

It adds:

- an exact polynomial relation `P - y = (X-z)Q`;
- the canonical honest quotient using `divByMonic`;
- proof that an exact quotient identity forces `P(z)=y`;
- the verifier-side local formula `Q(ξ)=(P(ξ)-y)/(ξ-z)` away from the pole;
- honest quotients for `V_a` at `γθ`, `Q_γ` at `θ`, and `V_c` at `γ`;
- reuse of the same scalar `y₁` between the first two relations;
- deterministic consistency theorems recovering
  `V_a(γθ)=y₁=Q(θ)` and `V_c(γ)=y₃`.

This remains purely algebraic.  It does not yet formalize root-counting
probabilities, correlated agreement, or FRI/proximity soundness.
