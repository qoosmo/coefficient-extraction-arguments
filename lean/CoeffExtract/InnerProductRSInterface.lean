import CoeffExtract.InnerProductInterface
import CoeffExtract.RSReversal

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- Verifier-side virtual reversal of the Reed--Solomon word for `b`. -/
noncomputable def virtualReversedRSWord
    {I F : Type*} [Field F] {N : Nat}
    (domain : I → F) (σ : I ≃ I) (b : Table F N) : I → F :=
  fun i =>
    (domain i) ^ (N - 1) *
      rsWord domain (tablePolynomial b) (σ i)

/-- The virtual reversal is exactly the RS word of the fixed-length reversed
table polynomial. -/
theorem virtualReversedRSWord_eq
    {I F : Type*} [Field F] {N : Nat}
    (domain : I → F) (σ : I ≃ I)
    (hInv : ∀ i, domain (σ i) = (domain i)⁻¹)
    (hNZ : ∀ i, domain i ≠ 0)
    (b : Table F N) :
    virtualReversedRSWord domain σ b =
      rsWord domain (reversedTablePolynomial b) := by
  funext i
  unfold virtualReversedRSWord
  exact (rsWord_reversal b domain σ hInv hNZ i).symm

/-- RS word of the canonical low witness `A`. -/
noncomputable def innerProductLowRSWord
    {I F : Type*} [Field F] {N : Nat}
    (domain : I → F) (a b : Table F N) : I → F :=
  rsWord domain (innerProductLowPolynomial a b)

/-- RS word of the canonical high witness `H`. -/
noncomputable def innerProductHighRSWord
    {I F : Type*} [Field F] {N : Nat}
    (domain : I → F) (a b : Table F N) : I → F :=
  rsWord domain (innerProductHighPolynomial a b)

/-- Pointwise virtual high-part formula used by the verifier. -/
def virtualInnerProductHighValue
    {F : Type*} [Field F] (N : Nat)
    (ξ wa wbStar wA S : F) : F :=
  (ξ * wa * wbStar - wA - S * ξ ^ N) / ξ ^ (N + 1)

/-- Evaluation of the canonical inner-product opening identity at an arbitrary
field point. -/
theorem eval_innerProduct_opening_identity
    {F : Type*} [Field F] {N : Nat}
    (hN : 0 < N) (a b : Table F N) (ξ : F) :
    ξ * (tablePolynomial a).eval ξ *
        (reversedTablePolynomial b).eval ξ =
      (innerProductLowPolynomial a b).eval ξ +
        dot a b * ξ ^ N +
        ξ ^ (N + 1) *
          (innerProductHighPolynomial a b).eval ξ := by
  have h := congrArg (fun p : Polynomial F => p.eval ξ)
    (innerProduct_opening_identity hN a b)
  simpa [innerProductPolynomial, innerProductClaimPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, mul_assoc] using h

/-- The verifier's virtual high-part formula equals the honest evaluation of
`H` whenever the claim is the true inner product. -/
theorem virtualInnerProductHighValue_eq_eval
    {F : Type*} [Field F] {N : Nat}
    (hN : 0 < N) (a b : Table F N)
    (ξ : F) (hξ : ξ ≠ 0) :
    virtualInnerProductHighValue N ξ
        ((tablePolynomial a).eval ξ)
        ((reversedTablePolynomial b).eval ξ)
        ((innerProductLowPolynomial a b).eval ξ)
        (dot a b) =
      (innerProductHighPolynomial a b).eval ξ := by
  unfold virtualInnerProductHighValue
  apply (div_eq_iff (pow_ne_zero _ hξ)).2
  have h := eval_innerProduct_opening_identity hN a b ξ
  rw [h]
  ring

/-- Word-level form of the virtual high-part identity on an inversion-closed
RS domain.  The verifier reads `a` and `A` at `i`, obtains the reversed value
of `b` virtually through `σ`, and recovers exactly the RS word of `H`. -/
theorem virtualInnerProductHighValue_eq_rsWord
    {I F : Type*} [Field F] {N : Nat}
    (hN : 0 < N)
    (domain : I → F) (σ : I ≃ I)
    (hInv : ∀ i, domain (σ i) = (domain i)⁻¹)
    (hNZ : ∀ i, domain i ≠ 0)
    (a b : Table F N) (i : I) :
    virtualInnerProductHighValue N (domain i)
        (rsWord domain (tablePolynomial a) i)
        (virtualReversedRSWord domain σ b i)
        (innerProductLowRSWord domain a b i)
        (dot a b) =
      innerProductHighRSWord domain a b i := by
  rw [show virtualReversedRSWord domain σ b i =
      rsWord domain (reversedTablePolynomial b) i by
        exact congrFun
          (virtualReversedRSWord_eq domain σ hInv hNZ b) i]
  simp only [rsWord_apply, innerProductLowRSWord,
    innerProductHighRSWord]
  exact virtualInnerProductHighValue_eq_eval
    hN a b (domain i) (hNZ i)

/-- Explicit verifier-side reversal formula, matching Section 8 of the paper:
`w_b^*(ξ) = ξ^(N-1) w_b(ξ^{-1})`, with inversion represented by `σ`. -/
theorem virtualReversedRSWord_apply
    {I F : Type*} [Field F] {N : Nat}
    (domain : I → F) (σ : I ≃ I)
    (b : Table F N) (i : I) :
    virtualReversedRSWord domain σ b i =
      (domain i) ^ (N - 1) *
        rsWord domain (tablePolynomial b) (σ i) := rfl

end CoeffExtract
