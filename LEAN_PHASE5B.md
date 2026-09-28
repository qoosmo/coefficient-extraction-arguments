# Lean Phase 5B — virtual reversal and RS-word inner-product interface

This phase bridges the algebraic inner-product layer to the verifier-side
Reed--Solomon word identities used in Section 8 of the paper.

It adds:

- `virtualReversedRSWord`;
- equality between that virtual word and the RS word of `V_b^*`;
- RS words for the canonical low and high witnesses;
- the verifier's virtual high-part formula;
- evaluation of the inner-product opening identity at an arbitrary field point;
- proof that the virtual high-part formula equals the honest evaluation of `H`;
- the complete word-level theorem on an inversion-closed RS domain.

This still does not formalize Merkle commitments, proximity testing, folding,
or probabilistic soundness.  It is the deterministic algebraic/word bridge
needed before those protocol layers.
