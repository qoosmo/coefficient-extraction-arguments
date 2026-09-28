import CoeffExtract.InnerProductRSInterface

open scoped BigOperators
open Polynomial

namespace CoeffExtract

/-- Geometric scaling of a table by the challenge `γ`:
coefficient `i` is multiplied by `γ^i`. -/
def geometricScale
    {F : Type*} [Monoid F] {N : Nat}
    (γ : F) (a : Table F N) : Table F N :=
  fun i => γ ^ i.1 * a i

@[simp] theorem geometricScale_apply
    {F : Type*} [Monoid F] {N : Nat}
    (γ : F) (a : Table F N) (i : Fin N) :
    geometricScale γ a i = γ ^ i.1 * a i := rfl

/-- Polynomial `Q_γ(X) = V_a(γX)` represented through its coefficient
table. -/
noncomputable def scaledTablePolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a : Table F N) : Polynomial F :=
  tablePolynomial (geometricScale γ a)

/-- Geometrically weighted bilinear sum used to compress a Hadamard
relation. -/
def weightedHadamardSum
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a b : Table F N) : F :=
  ∑ i : Fin N, γ ^ i.1 * a i * b i

/-- Evaluating the scaled coefficient polynomial at `x` is equivalent to
evaluating the original table polynomial at `γx`. -/
theorem eval_scaledTablePolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a : Table F N) (x : F) :
    (scaledTablePolynomial γ a).eval x =
      (tablePolynomial a).eval (γ * x) := by
  classical
  simp only [scaledTablePolynomial, eval_tablePolynomial, evalTable,
    geometricScale_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  ring

/-- The dot product of the geometrically scaled first table with `b` is the
weighted bilinear sum. -/
theorem dot_geometricScale_eq_weightedHadamardSum
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a b : Table F N) :
    dot (geometricScale γ a) b = weightedHadamardSum γ a b := by
  simp [dot, weightedHadamardSum, geometricScale, mul_assoc]

/-- Weighted Hadamard coefficient identity from Section 9:
`[X^(N-1)] V_a(γX) V_b^*(X) = Σ γ^i a_i b_i`. -/
theorem coeff_scaledTablePolynomial_mul_reversed_eq_weightedHadamardSum
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (γ : F) (a b : Table F N) :
    (scaledTablePolynomial γ a * reversedTablePolynomial b).coeff (N - 1) =
      weightedHadamardSum γ a b := by
  unfold scaledTablePolynomial
  rw [coeff_tablePolynomial_mul_reversed_eq_dot hN]
  exact dot_geometricScale_eq_weightedHadamardSum γ a b

/-- Paper-oriented orientation of the weighted coefficient identity. -/
theorem weightedHadamardSum_eq_coeff
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (γ : F) (a b : Table F N) :
    weightedHadamardSum γ a b =
      (scaledTablePolynomial γ a * reversedTablePolynomial b).coeff (N - 1) :=
  (coeff_scaledTablePolynomial_mul_reversed_eq_weightedHadamardSum
    hN γ a b).symm

/-- Weighted sum of one table is its table-polynomial evaluation. -/
theorem weightedTableSum_eq_eval
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (c : Table F N) :
    (∑ i : Fin N, γ ^ i.1 * c i) =
      (tablePolynomial c).eval γ := by
  classical
  rw [eval_tablePolynomial]
  unfold evalTable
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A true coordinatewise Hadamard relation remains true after geometric
compression. -/
theorem weightedHadamardSum_eq_eval_of_hadamard
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a b c : Table F N)
    (h : hadamard a b = c) :
    weightedHadamardSum γ a b =
      (tablePolynomial c).eval γ := by
  subst c
  rw [← weightedTableSum_eq_eval γ (hadamard a b)]
  simp [weightedHadamardSum, hadamard, mul_assoc]

/-- Compressed Hadamard coefficient relation:
if `a ∘ b = c`, then `V_c(γ)` is the middle coefficient of
`V_a(γX) V_b^*(X)`. -/
theorem hadamard_compressed_coefficient
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (γ : F) (a b c : Table F N)
    (h : hadamard a b = c) :
    (scaledTablePolynomial γ a * reversedTablePolynomial b).coeff (N - 1) =
      (tablePolynomial c).eval γ := by
  rw [coeff_scaledTablePolynomial_mul_reversed_eq_weightedHadamardSum
    hN γ a b]
  exact weightedHadamardSum_eq_eval_of_hadamard γ a b c h

/-- Product polynomial used by the compressed Hadamard opening. -/
noncomputable def hadamardCompressedPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a b : Table F N) : Polynomial F :=
  innerProductPolynomial (geometricScale γ a) b

/-- Canonical low split witness for the compressed Hadamard opening. -/
noncomputable def hadamardLowPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a b : Table F N) : Polynomial F :=
  innerProductLowPolynomial (geometricScale γ a) b

/-- Canonical high split witness for the compressed Hadamard opening. -/
noncomputable def hadamardHighPolynomial
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a b : Table F N) : Polynomial F :=
  innerProductHighPolynomial (geometricScale γ a) b

/-- Canonical opening identity for a true Hadamard relation after geometric
compression. -/
theorem hadamard_opening_identity
    {F : Type*} [CommRing F] {N : Nat}
    (hN : 0 < N) (γ : F) (a b c : Table F N)
    (h : hadamard a b = c) :
    Polynomial.X * hadamardCompressedPolynomial γ a b =
      hadamardLowPolynomial γ a b +
        Polynomial.C ((tablePolynomial c).eval γ) * Polynomial.X ^ N +
        Polynomial.X ^ (N + 1) * hadamardHighPolynomial γ a b := by
  have hip :=
    innerProduct_opening_identity hN (geometricScale γ a) b
  have hv :
      dot (geometricScale γ a) b =
        (tablePolynomial c).eval γ := by
    rw [dot_geometricScale_eq_weightedHadamardSum]
    exact weightedHadamardSum_eq_eval_of_hadamard γ a b c h
  rw [hv] at hip
  simpa [hadamardCompressedPolynomial, hadamardLowPolynomial,
    hadamardHighPolynomial, innerProductClaimPolynomial] using hip

/-- Exact compressed scalar carried by a true Hadamard relation. -/
theorem hadamard_compressed_value_eq_dot
    {F : Type*} [CommRing F] {N : Nat}
    (γ : F) (a b c : Table F N)
    (h : hadamard a b = c) :
    dot (geometricScale γ a) b =
      (tablePolynomial c).eval γ := by
  rw [dot_geometricScale_eq_weightedHadamardSum]
  exact weightedHadamardSum_eq_eval_of_hadamard γ a b c h

end CoeffExtract
