import CoeffExtract.PolynomialBridge

namespace CoeffExtract

/-- Reversal equivalence on `Fin N`.  It packages the involution proved in
Phase 1 as a reusable equivalence for reindexing finite sums. -/
def revEquiv (N : Nat) : Fin N ≃ Fin N where
  toFun := revIndex
  invFun := revIndex
  left_inv := revIndex_involutive
  right_inv := revIndex_involutive

@[simp] theorem revEquiv_apply {N : Nat} (i : Fin N) :
    revEquiv N i = revIndex i := rfl

@[simp] theorem revEquiv_symm_apply {N : Nat} (i : Fin N) :
    (revEquiv N).symm i = revIndex i := rfl

/-- Abstract word-level reversal induced by a permutation of positions.  For
an inversion-closed Reed--Solomon domain, `σ` will be inversion. -/
def permuteWord {I F : Type*} (σ : I ≃ I) (w : I → F) : I → F :=
  fun i => w (σ i)

@[simp] theorem permuteWord_apply {I F : Type*}
    (σ : I ≃ I) (w : I → F) (i : I) :
    permuteWord σ w i = w (σ i) := rfl

/-- A position permutation preserves equality pointwise after applying the
same permutation to both words. -/
theorem permuteWord_eq_iff {I F : Type*}
    (σ : I ≃ I) (u v : I → F) (i : I) :
    permuteWord σ u i = permuteWord σ v i ↔ u (σ i) = v (σ i) := by
  rfl

/-- An involutive position permutation induces an involution on words. -/
theorem permuteWord_involutive {I F : Type*}
    (σ : I ≃ I) (hσ : ∀ i, σ (σ i) = i) (w : I → F) :
    permuteWord σ (permuteWord σ w) = w := by
  funext i
  simp [permuteWord, hσ]

/-- Coefficient reversal is exactly the position permutation `revEquiv` on a
finite coefficient word. -/
theorem reverse_eq_permuteWord_revEquiv {F : Type*} {N : Nat}
    (t : Table F N) :
    reverse t = permuteWord (revEquiv N) t := by
  rfl

end CoeffExtract
