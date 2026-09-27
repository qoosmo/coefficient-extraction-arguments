import CoeffExtract.PolynomialBridge
import Mathlib.Data.Nat.Bitwise

open scoped BigOperators

namespace CoeffExtract

/-- Boolean equality weight associated with the binary index `j` and an
arbitrary evaluation point `z`.  Bit `i` contributes `z_i` when it is one and
`1-z_i` when it is zero. -/
def mleWeight {F : Type*} [CommRing F] {n : Nat}
    (z : Fin n → F) (j : Fin (2 ^ n)) : F :=
  ∏ i : Fin n, if Nat.testBit j.1 i.1 then z i else 1 - z i

/-- The table of Boolean equality weights `w ↦ eq(w,z)` in the paper's fixed
binary ordering. -/
def mleWeightTable {F : Type*} [CommRing F] (n : Nat)
    (z : Fin n → F) : Table F (2 ^ n) :=
  fun j => mleWeight z j

/-- Coefficient table of the public MLE kernel.  The reversal is exactly what
turns the dot product against equality weights into the middle coefficient. -/
def mleKernelCoeffs {F : Type*} [CommRing F] (n : Nat)
    (z : Fin n → F) : Table F (2 ^ n) :=
  reverse (mleWeightTable n z)

/-- Polynomial realization of the MLE public kernel. -/
noncomputable def mleKernelPolynomial {F : Type*} [CommRing F] (n : Nat)
    (z : Fin n → F) : Polynomial F :=
  tablePolynomial (mleKernelCoeffs n z)

/-- The core table-MLE coefficient identity: pairing a table with the reversed
Boolean equality-weight table extracts its multilinear evaluation functional. -/
theorem middleCoeff_mleKernel_eq
    {F : Type*} [CommRing F] (n : Nat)
    (t : Table F (2 ^ n)) (z : Fin n → F) :
    middleCoeff t (mleKernelCoeffs n z) =
      ∑ j : Fin (2 ^ n), t j * mleWeight z j := by
  simpa [mleKernelCoeffs, mleWeightTable, dot] using
    (middleCoeff_reverse_eq_dot t (mleWeightTable n z))

/-- The coefficient of the polynomial MLE kernel is the reversed equality
weight. -/
@[simp] theorem mleKernelPolynomial_coeff_fin
    {F : Type*} [CommRing F] (n : Nat)
    (z : Fin n → F) (j : Fin (2 ^ n)) :
    (mleKernelPolynomial n z).coeff j.1 =
      mleWeight z (revIndex j) := by
  simp [mleKernelPolynomial, mleKernelCoeffs, mleWeightTable]

end CoeffExtract
