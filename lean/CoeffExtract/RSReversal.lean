import CoeffExtract.VirtualReversal
import Mathlib.Algebra.GroupWithZero.Units.Basic

open scoped BigOperators

namespace CoeffExtract

/-- Reed--Solomon evaluation word of a polynomial on an indexed domain. -/
def rsWord {I F : Type*} [Semiring F]
    (domain : I → F) (p : Polynomial F) : I → F :=
  fun i => p.eval (domain i)

@[simp] theorem rsWord_apply {I F : Type*} [Semiring F]
    (domain : I → F) (p : Polynomial F) (i : I) :
    rsWord domain p i = p.eval (domain i) := rfl

/-- Evaluation identity for the fixed-length coefficient reversal:
`V*(ξ) = ξ^(N-1) V(ξ⁻¹)`.  Unlike `Polynomial.reverse`, this theorem uses the
paper's ambient length `N`, so leading zero coefficients are preserved. -/
theorem eval_reversedTablePolynomial
    {F : Type*} [Field F] {N : Nat}
    (t : Table F N) (ξ : F) (hξ : ξ ≠ 0) :
    (reversedTablePolynomial t).eval ξ =
      ξ ^ (N - 1) * (tablePolynomial t).eval ξ⁻¹ := by
  classical
  simp only [reversedTablePolynomial, eval_tablePolynomial, evalTable, reverse_apply]
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (revEquiv N)
    (fun i : Fin N => ξ ^ (N - 1) * (t i * (ξ⁻¹) ^ i.1))]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [revEquiv_apply]
  have hrevle : N - 1 - i.1 ≤ N - 1 := Nat.sub_le _ _
  have hsub : (N - 1) - (N - 1 - i.1) = i.1 := by omega
  have hpow :
      ξ ^ ((N - 1) - (N - 1 - i.1)) =
        ξ ^ (N - 1) * (ξ ^ (N - 1 - i.1))⁻¹ :=
    pow_sub₀ ξ hξ hrevle
  have hp :
      ξ ^ i.1 =
        ξ ^ (N - 1) * (ξ ^ (N - 1 - i.1))⁻¹ := by
    simpa only [hsub] using hpow
  rw [revIndex_val, inv_pow, hp]
  ring

/-- Exact virtual Reed--Solomon reversal on an inversion-closed domain.
If `σ` realizes inversion on the domain, the reversed polynomial word is
obtained from the original word by permuting positions with `σ` and applying
the public multiplier `ξ^(N-1)`. -/
theorem rsWord_reversal
    {I F : Type*} [Field F] {N : Nat}
    (t : Table F N) (domain : I → F) (σ : I ≃ I)
    (hInv : ∀ i, domain (σ i) = (domain i)⁻¹)
    (hNZ : ∀ i, domain i ≠ 0) (i : I) :
    rsWord domain (reversedTablePolynomial t) i =
      (domain i) ^ (N - 1) *
        rsWord domain (tablePolynomial t) (σ i) := by
  rw [rsWord_apply, eval_reversedTablePolynomial t (domain i) (hNZ i)]
  simp only [rsWord_apply, hInv]

end CoeffExtract
