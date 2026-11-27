import TwoAxisHelicoid.FourierCoefficients
import Mathlib.Data.Rat.BigOperators

namespace TwoAxisHelicoid.VerticalRun

def piLower : ℚ := 314159265358979323846264338327950288419716 / 10^41
def piUpper : ℚ := 314159265358979323846264338327950288419717 / 10^41

def expCut (N : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range N, x^k / (k.factorial : ℚ)

def expError (N : ℕ) (x : ℚ) : ℚ := |x|^N / (N.factorial : ℚ) * 2

abbrev ExpTest (N : ℕ) (t lo hi : ℚ) : Prop :=
  let a := -piUpper*t
  let b := -piLower*t
  |a| / ((N : ℚ)+1) ≤ 1/2 ∧ |b| / ((N : ℚ)+1) ≤ 1/2 ∧
  lo ≤ expCut N a - expError N a ∧ expCut N b + expError N b ≤ hi

def seriesCut (N : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ Finset.range N, (fourierCoefficientAt (i+1) : ℚ)*q^(i+1)

def seriesTail (N : ℕ) (q : ℚ) : ℚ :=
  q^(N+1) * (((N : ℚ)+1)^2/(1-q) + 2*((N : ℚ)+1)*q/(1-q)^2 + q*(1+q)/(1-q)^3)

abbrev SeriesTest (N : ℕ) (lo hi L U : ℚ) : Prop :=
  L < 1/4 - 2*(seriesCut N hi + seriesTail N hi) ∧ 1/4 - 2*seriesCut N lo < U

end TwoAxisHelicoid.VerticalRun

#print axioms TwoAxisHelicoid.VerticalRun.expCut
#print axioms TwoAxisHelicoid.VerticalRun.seriesCut
