import CoeffExtract.Reversal

open scoped BigOperators

namespace CoeffExtract

/-- Coefficient-level model of `[X^(N-1)] U(X) K(X)` for two polynomials
whose coefficient vectors have length `N`.  The second vector is indexed in
reverse because the pairs contributing to degree `N-1` are `(i,N-1-i)`. -/
def middleCoeff {F : Type*} [Semiring F] {N : Nat}
    (u k : Table F N) : F :=
  ∑ i : Fin N, u i * k (revIndex i)

/-- The classical middle-coefficient inner-product identity from Section 4:
`[X^(N-1)] V_a(X) V_b*(X) = ⟨a,b⟩`. -/
theorem middleCoeff_reverse_eq_dot {F : Type*} [Semiring F] {N : Nat}
    (a b : Table F N) :
    middleCoeff a (reverse b) = dot a b := by
  simp [middleCoeff, reverse, dot]

/-- Public linear functionals are the same middle-coefficient identity with
one public vector. -/
theorem publicLinearFunctional {F : Type*} [Semiring F] {N : Nat}
    (a p : Table F N) :
    middleCoeff a (reverse p) = ∑ i : Fin N, a i * p i := by
  simpa [dot] using middleCoeff_reverse_eq_dot a p

/-- Hypercube sum is the public linear functional against the all-ones table. -/
theorem hypercubeSum {F : Type*} [Semiring F] {N : Nat}
    (a : Table F N) :
    middleCoeff a (reverse (fun _ => (1 : F))) = ∑ i : Fin N, a i := by
  simp [middleCoeff, reverse]

end CoeffExtract
