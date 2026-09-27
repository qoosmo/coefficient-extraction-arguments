import CoeffExtract.CoefficientIdentity

namespace CoeffExtract

/-- Coefficient sequence of multiplication by `X`: degree `r` after the shift
is coefficient `r-1` before the shift, with zero at degree zero. -/
def xShift {F : Type*} [Zero F] (c : Nat → F) (r : Nat) : F :=
  if r = 0 then 0 else c (r - 1)

/-- Low part `A` of the universal split. -/
def splitLow {F : Type*} [Zero F] (N : Nat) (c : Nat → F) : Table F N :=
  fun i => xShift c i.1

/-- Selected coefficient `v = [X^(N-1)] UK`, equivalently the degree-`N`
coefficient after multiplication by `X`. -/
def splitValue {F : Type*} [Zero F] (N : Nat) (c : Nat → F) : F :=
  xShift c N

/-- High part `H`: its coefficient `i` is the shifted-product coefficient at
`N+1+i`. -/
def splitHigh {F : Type*} [Zero F] (N : Nat) (c : Nat → F) : Table F N :=
  fun i => xShift c (N + 1 + i.1)

/-- Coefficient sequence reconstructed from `(A,v,H)` in
`A + v X^N + X^(N+1) H`. -/
def recombineSplit {F : Type*} [Zero F] [Add F]
    (N : Nat) (A : Table F N) (v : F) (H : Table F N) (r : Nat) : F :=
  if hA : r < N then A ⟨r, hA⟩
  else if hV : r = N then v
  else if hH : r < 2 * N then H ⟨r - (N + 1), by omega⟩
  else 0

/-- Coefficient form of the universal split theorem.  It is intentionally
stated for an arbitrary coefficient sequence `c` with the product-support
bound `c r = 0` for `r ≥ 2N-1`; later modules instantiate `c` with the
coefficients of `U*K`. -/
theorem universalSplitCoeff {F : Type*} [AddMonoid F]
    (N : Nat) (c : Nat → F)
    (hsupp : ∀ r, 2 * N - 1 ≤ r → c r = 0) (r : Nat) :
    xShift c r =
      recombineSplit N (splitLow N c) (splitValue N c) (splitHigh N c) r := by
  by_cases hN : N = 0
  · subst N
    by_cases hr : r = 0
    · subst r
      simp [xShift, recombineSplit, splitLow, splitValue, splitHigh]
    · have hc : c (r - 1) = 0 := hsupp (r - 1) (by omega)
      simp [xShift, recombineSplit, splitLow, splitValue, splitHigh, hr, hc]
  by_cases h0 : r = 0
  · subst r
    simp [xShift, recombineSplit, splitLow, splitValue, splitHigh, hN]
  by_cases hA : r < N
  · simp [recombineSplit, hA, splitLow]
  by_cases hV : r = N
  · subst r
    simp [recombineSplit, splitValue]
  by_cases hH : r < 2 * N
  · have hN1 : N + 1 ≤ r := by omega
    simp [recombineSplit, hA, hV, hH, splitHigh]
    congr 1
    omega
  · have hr : 2 * N ≤ r := by omega
    have hs : 2 * N - 1 ≤ r - 1 := by omega
    have hc : c (r - 1) = 0 := hsupp (r - 1) hs
    simp [recombineSplit, hA, hV, hH, xShift, h0, hc]

/-- The split's middle value is exactly the pre-shift coefficient `N-1`. -/
theorem splitValue_eq {F : Type*} [Zero F]
    (N : Nat) (c : Nat → F) (hN : 0 < N) :
    splitValue N c = c (N - 1) := by
  simp [splitValue, xShift]
  omega

end CoeffExtract
