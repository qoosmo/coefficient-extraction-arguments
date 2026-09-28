import CoeffExtract.PolynomialUniversalSplit

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- Product polynomial used by the committed inner-product protocol:
`V_a(X) V_b^*(X)`. -/
noncomputable def innerProductPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (a b : Table F N) : Polynomial F :=
  tablePolynomial a * reversedTablePolynomial b

/-- Canonical low witness `A` for the committed inner-product split. -/
noncomputable def innerProductLowPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (a b : Table F N) : Polynomial F :=
  splitLowPolynomial N (innerProductPolynomial a b).coeff

/-- Canonical high witness `H` for the committed inner-product split. -/
noncomputable def innerProductHighPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (a b : Table F N) : Polynomial F :=
  splitHighPolynomial N (innerProductPolynomial a b).coeff

/-- Right-hand side of the algebraic opening identity for a claimed
inner-product value `S`. -/
noncomputable def innerProductClaimPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (a b : Table F N) (S : F) : Polynomial F :=
  innerProductLowPolynomial a b +
    Polynomial.C S * Polynomial.X ^ N +
    Polynomial.X ^ (N + 1) * innerProductHighPolynomial a b

/-- The selected coefficient in the universal split of
`V_a V_b^*` is the table inner product. -/
theorem innerProduct_splitValue_eq_dot
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a b : Table F N) :
    splitValue N (innerProductPolynomial a b).coeff = dot a b := by
  unfold innerProductPolynomial reversedTablePolynomial
  rw [splitValue_tablePolynomial_mul_eq_middleCoeff hN]
  exact middleCoeff_reverse_eq_dot a b

/-- Canonical algebraic opening identity for committed inner products:
`X V_a V_b^* = A + <a,b> X^N + X^(N+1) H`. -/
theorem innerProduct_opening_identity
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a b : Table F N) :
    Polynomial.X * innerProductPolynomial a b =
      innerProductClaimPolynomial a b (dot a b) := by
  have h :=
    universalSplit_tablePolynomial_mul
      (F := F) a (reverse b)
  have hv :
      splitValue N
          (tablePolynomial a * tablePolynomial (reverse b)).coeff =
        dot a b := by
    rw [splitValue_tablePolynomial_mul_eq_middleCoeff hN a (reverse b)]
    exact middleCoeff_reverse_eq_dot a b
  unfold recombineSplitPolynomial at h
  rw [hv] at h
  simpa [innerProductPolynomial, innerProductClaimPolynomial,
    innerProductLowPolynomial, innerProductHighPolynomial,
    reversedTablePolynomial] using h

/-- The coefficient at degree `N` of the claimed right-hand side is exactly
the claimed scalar `S`. -/
theorem coeff_innerProductClaimPolynomial_middle
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a b : Table F N) (S : F) :
    (innerProductClaimPolynomial a b S).coeff N = S := by
  unfold innerProductClaimPolynomial innerProductLowPolynomial
    innerProductHighPolynomial
  have hlow :
      (splitLowPolynomial N (innerProductPolynomial a b).coeff).coeff N = 0 := by
    unfold splitLowPolynomial
    exact tablePolynomial_coeff_eq_zero_of_ge _ (le_refl N)
  have hshift : ¬ N + 1 ≤ N := by omega
  rw [Polynomial.coeff_add, Polynomial.coeff_add, hlow]
  rw [Polynomial.coeff_C_mul_X_pow]
  simp only [if_pos rfl, zero_add]
  rw [Polynomial.coeff_X_pow_mul']
  simp [hshift]

/-- The coefficient at degree `N` of the left-hand side is the actual inner
product. -/
theorem coeff_X_innerProductPolynomial_middle
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a b : Table F N) :
    (Polynomial.X * innerProductPolynomial a b).coeff N = dot a b := by
  rw [coeff_X_mul_eq_xShift]
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  simp only [xShift, if_neg hN0]
  unfold innerProductPolynomial
  exact coeff_tablePolynomial_mul_reversed_eq_dot hN a b

/-- Algebraic binding of the committed inner-product opening identity:
with the canonical low/high split witnesses, an identity carrying claim `S`
can hold only for the true inner product. -/
theorem innerProduct_claim_eq_dot_of_opening_identity
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a b : Table F N) (S : F)
    (h :
      Polynomial.X * innerProductPolynomial a b =
        innerProductClaimPolynomial a b S) :
    S = dot a b := by
  have hc := congrArg (fun p : Polynomial F => p.coeff N) h
  rw [coeff_X_innerProductPolynomial_middle hN a b,
      coeff_innerProductClaimPolynomial_middle hN a b S] at hc
  exact hc.symm

/-- Exact algebraic characterization of a committed inner-product claim using
the canonical universal-split witnesses. -/
theorem innerProduct_opening_identity_iff
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (a b : Table F N) (S : F) :
    Polynomial.X * innerProductPolynomial a b =
        innerProductClaimPolynomial a b S
      ↔ S = dot a b := by
  constructor
  · exact innerProduct_claim_eq_dot_of_opening_identity hN a b S
  · intro hS
    subst S
    exact innerProduct_opening_identity hN a b

end CoeffExtract
