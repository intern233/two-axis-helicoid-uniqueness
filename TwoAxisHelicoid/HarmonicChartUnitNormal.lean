import TwoAxisHelicoid.SurfaceDotLaplacian
import TwoAxisHelicoid.MinimalChartComplexData

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace
open scoped Topology

noncomputable def harmonicChartNormal (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  let A := planePartial 1 X z
  let B := planePartial I X z
  (A ⬝ᵥ A)⁻¹ • (A ⨯₃ B)

/-- The oriented normal is an actual analytic unit normal computed from
the chart derivatives. The inverse squared tangent length is regular at
every regular conformal point. -/
theorem harmonicChartNormal_data {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : AnalyticAt ℝ X z) (hc : ConformalCoordinateDerivatives X z)
    (hi : Function.Injective (fderiv ℝ X z)) :
    let A := planePartial 1 X z
    let B := planePartial I X z
    let N := harmonicChartNormal X z
    AnalyticAt ℝ (harmonicChartNormal X) z ∧ 0 < A ⬝ᵥ A ∧ A ⬝ᵥ A = B ⬝ᵥ B ∧ A ⬝ᵥ B = 0 ∧
      N = unitCrossNormal A B ∧ N ⬝ᵥ N = 1 ∧ N ⬝ᵥ A = 0 ∧ N ⬝ᵥ B = 0 := by
  let A := planePartial 1 X
  let B := planePartial I X
  have hA := planePartial_analyticAt hX 1
  have hB := planePartial_analyticAt hX I
  have hn : A z ≠ 0 := fun h => one_ne_zero (hi (h.trans (fderiv ℝ X z).map_zero.symm))
  have hp : 0 < A z ⬝ᵥ A z := lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (A z j))
    (fun h => hn (dotProduct_self_eq_zero.mp h.symm))
  obtain ⟨hab,hperp⟩ := (conformalCoordinateDerivatives_iff_dot hX.differentiableAt).mp hc
  have hg : AnalyticAt ℝ (fun w => A w ⬝ᵥ A w) z := (spatialDotBilinear.analyticAt_bilinear (A z,A z)).comp₂ hA hA
  have hn' : AnalyticAt ℝ (fun w => A w ⨯₃ B w) z := (spatialCrossBilinear.analyticAt_bilinear (A z,B z)).comp₂ hA hB
  have hN : AnalyticAt ℝ (harmonicChartNormal X) z := (hg.inv hp.ne').smul hn'
  have hnormal : harmonicChartNormal X z = unitCrossNormal (A z) (B z) := by
    have hb : B z ⬝ᵥ B z = A z ⬝ᵥ A z := hab.symm
    have hp' : A z ⬝ᵥ B z = 0 := hperp
    unfold unitCrossNormal
    rw [cross_dot_cross,hb,hp',zero_mul,sub_zero,← pow_two,Real.sqrt_sq hp.le]
    rfl
  refine ⟨hN,hp,hab,hperp,hnormal,?_⟩
  rw [hnormal]
  exact conformal_unitCrossNormal hp rfl hab.symm hperp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonicChartNormal_data
