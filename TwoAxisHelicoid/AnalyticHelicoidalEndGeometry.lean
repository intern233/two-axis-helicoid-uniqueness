import TwoAxisHelicoid.HeightEndVerticalCoordinate
import TwoAxisHelicoid.HeightEndEmbedding
import TwoAxisHelicoid.HeightEndCurvature
import TwoAxisHelicoid.ActualAreaVariationIndex

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- Analytic helicoidal differential data alone force a proper embedded
subend with bounded Gaussian curvature. The third coordinate is derived
on the connected exterior, rather than assumed separately. -/
theorem analytic_helicoidal_end_embedded_bounded_curvature
    {X : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} {α R₀ : ℝ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*(α : ℂ)*z+infinityCorrection f z)) 1)) z) :
    ∃ R : ℝ, R₀ < R ∧
      IsProperMap (fun z : {z : ℂ // R ≤ ‖z‖} => X z.1) ∧
      IsClosedEmbedding (fun z : {z : ℂ // R ≤ ‖z‖} => X z.1) ∧
      ∀ z : ℂ, R ≤ ‖z‖ →
        |logGaussGaussianCurvature (fun z => I*(α : ℂ)*z+infinityCorrection f z) z| ≤ (|α|+1)^2 := by
  obtain ⟨A,_,hA⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (analytic_height_end_curvature_bounded α hf)
  let S := max 0 (max R₀ A)
  have hS : 0 ≤ S := le_max_left _ _
  have hRS : R₀ ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hAS : A ≤ S := (le_max_right _ _).trans (le_max_right _ _)
  have hd z (hz : S < ‖z‖) := hX z (hRS.trans_lt hz)
  obtain ⟨b,hb⟩ := height_end_third_coordinate hS hd
  have hF := infinityCorrection_tendsto_zero hf hf0
  obtain ⟨R,hR,hEmb⟩ := height_normalized_helicoidal_end_eventually_embedded α b S hd hb hF
  exact ⟨R,hRS.trans_lt hR,height_normalized_helicoidal_end_isProperMap α b S R hR hd hb hF,
    hEmb,fun z hz => hA (hAS.trans (hR.le.trans hz))⟩

/-- The same actual analytic end supports arbitrary-dimensional negative
spaces for the second derivative of compact normal area integrals. -/
theorem analytic_helicoidal_end_actual_area_index
    {X : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} {α R₀ : ℝ}
    (hα : α ≠ 0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*(α : ℂ)*z+infinityCorrection f z)) 1)) z) :
    HasInfiniteCompactActualAreaIndexAtInfinity X
      (fun z => I*(α : ℂ)*z+infinityCorrection f z) := by
  apply analytic_helicoid_actual_area_infinite_index hα hf hf0 (B := R₀+1)
  intro p hp
  exact hX (planeComplex p) (by linarith [norm_le_planeComplex_norm p])

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_helicoidal_end_embedded_bounded_curvature
#print axioms TwoAxisHelicoid.analytic_helicoidal_end_actual_area_index
