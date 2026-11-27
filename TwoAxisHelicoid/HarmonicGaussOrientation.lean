import TwoAxisHelicoid.HarmonicCoordinateSigns
import TwoAxisHelicoid.NullGaussOrientation

namespace TwoAxisHelicoid
open Complex Set

def verticalHalfTurnSigns : Fin 3 → ℝ := ![-1,-1,1]
def verticalPlaneReflectionSigns : Fin 3 → ℝ := ![1,-1,1]

theorem verticalHalfTurnSigns_sq (j : Fin 3) : (verticalHalfTurnSigns j)^2 = 1 := by
  fin_cases j <;> norm_num [verticalHalfTurnSigns]

theorem verticalPlaneReflectionSigns_sq (j : Fin 3) : (verticalPlaneReflectionSigns j)^2 = 1 := by
  fin_cases j <;> norm_num [verticalPlaneReflectionSigns]

theorem punctured_coefficient_vertical_reflection {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) {z : ℂ} (hz : z ∉ L.lattice) :
    puncturedImmersionCoefficient L (fun w => coordinateSignMap verticalPlaneReflectionSigns (X w)) z =
      flipNullY (puncturedImmersionCoefficient L X z) := by
  rw [coordinateSignMap_punctured_coefficient hX _ hz]
  ext j
  fin_cases j <;> simp [verticalPlaneReflectionSigns,flipNullY]

theorem punctured_coefficient_vertical_half_turn {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) {z : ℂ} (hz : z ∉ L.lattice) :
    puncturedImmersionCoefficient L (fun w => coordinateSignMap verticalHalfTurnSigns (X w)) z =
      ![-puncturedImmersionCoefficient L X z 0,-puncturedImmersionCoefficient L X z 1,
        puncturedImmersionCoefficient L X z 2] := by
  rw [coordinateSignMap_punctured_coefficient hX _ hz]
  ext j
  fin_cases j <;> simp [verticalHalfTurnSigns]

theorem nullGauss_vertical_half_turn (p : Fin 3 → ℂ) :
    nullGauss (![-p 0,-p 1,p 2]) = -nullGauss p := by
  have he : nullHorizontalMinus (![-p 0,-p 1,p 2]) = -nullHorizontalMinus p := by
    simp [nullHorizontalMinus]
    ring
  unfold nullGauss
  rw [he]
  change p 2/ -nullHorizontalMinus p = -(p 2/nullHorizontalMinus p)
  exact div_neg _

/-- The coefficient-level choice between p and its y-reflection is
realized by an actual ambient Euclidean isometry of the entire map. -/
theorem harmonic_coefficient_orientation_isometry {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    {q : ℂ → Fin 3 → ℂ}
    (hq : q = puncturedImmersionCoefficient L X ∨ q = fun z => flipNullY (puncturedImmersionCoefficient L X z)) :
    ∃ R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      (∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) ∧
      TwoAxisHarmonicConformalImmersion L (fun z => R (X z)) ∧
      ∀ z ∉ L.lattice, puncturedImmersionCoefficient L (fun z => R (X z)) z = q z := by
  rcases hq with rfl | rfl
  · exact ⟨Homeomorph.refl _,fun _ _ => rfl,hX,fun _ _ => rfl⟩
  · exact ⟨coordinateSignHomeomorph verticalPlaneReflectionSigns_sq,
      coordinateSignMap_squared_displacement verticalPlaneReflectionSigns_sq,
      hX.coordinateSigns verticalPlaneReflectionSigns_sq,
      fun _ hz => punctured_coefficient_vertical_reflection hX hz⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_coefficient_orientation_isometry
