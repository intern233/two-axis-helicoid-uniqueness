import TwoAxisHelicoid.HarmonicChartUnitNormal
import TwoAxisHelicoid.HarmonicNullLift
import TwoAxisHelicoid.SimilaritySymmetry

namespace TwoAxisHelicoid
open Complex Matrix
open scoped ComplexConjugate

private noncomputable def coefficientUnitNormal (p : Fin 3 → ℂ) : Fin 3 → ℝ :=
  let A := fun j => (p j).re
  let B := fun j => -(p j).im
  (A ⬝ᵥ A)⁻¹ • (A ⨯₃ B)

private theorem normal_of_actual_coefficient {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) {z : ℂ} (hz : z ∉ L.lattice) :
    harmonicChartNormal X z = coefficientUnitNormal (puncturedImmersionCoefficient L X z) := by
  let p := puncturedImmersionCoefficient L X z
  have h := (puncturedImmersionCoefficient_hasFDerivAt hX hz).fderiv
  have hr : planePartial 1 X z = fun j => (p j).re := by
    change fderiv ℝ X z 1 = _
    rw [h]
    ext j
    simp [p]
  have hi : planePartial I X z = fun j => -(p j).im := by
    change fderiv ℝ X z I = _
    rw [h]
    ext j
    simp [p,Complex.mul_re]
  unfold harmonicChartNormal
  rw [hr,hi]
  rfl

private theorem coefficientNormal_conj (p : Fin 3 → ℂ) :
    coefficientUnitNormal ![conj (p 0),-conj (p 1),-conj (p 2)] = -halfTurnX (coefficientUnitNormal p) := by
  ext j
  fin_cases j <;> simp [coefficientUnitNormal,halfTurnX,dotProduct,Fin.sum_univ_succ,cross_apply]
  all_goals ring

private theorem coefficientNormal_neg_conj (p : Fin 3 → ℂ) :
    coefficientUnitNormal ![conj (p 0),conj (p 1),-conj (p 2)] = -halfTurnZ (coefficientUnitNormal p) := by
  ext j
  fin_cases j <;> simp [coefficientUnitNormal,halfTurnZ,dotProduct,Fin.sum_univ_succ,cross_apply]
  all_goals ring

/-- The differentiated Weierstrass data of the actual immersion show that
both ambient half-turns reverse its chosen surface orientation. -/
theorem harmonic_axis_oriented_normals {L : PeriodPair} (hL : ConjugationInvariantLattice L)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X) {z : ℂ} (hz : z ∉ L.lattice) :
    harmonicChartNormal X (conj z) = -halfTurnX (harmonicChartNormal X z) ∧
      harmonicChartNormal X (-conj z) = -halfTurnZ (harmonicChartNormal X z) := by
  have hc : conj z ∉ L.lattice := fun h => hz (by simpa using hL (conj z) h)
  have hn : -conj z ∉ L.lattice := by simpa using hc
  have hcon := puncturedImmersionCoefficient_conjugation hL hX hz
  rw [normal_of_actual_coefficient hX hc,normal_of_actual_coefficient hX hn,normal_of_actual_coefficient hX hz,
    puncturedImmersionCoefficient_neg hX hc,hcon]
  constructor
  · exact coefficientNormal_conj _
  · simpa using coefficientNormal_neg_conj (puncturedImmersionCoefficient L X z)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_axis_oriented_normals
