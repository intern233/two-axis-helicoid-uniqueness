import TwoAxisHelicoid.OriginalExteriorTorusReduction

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology Manifold

/-- Deep points of the geometric height chart miss every fixed compact
subset of the original surface. Both ends of the coordinate annulus are
distinguished using the actual height function. -/
theorem geometric_exterior_inverse_escapes {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (X : M → Fin 3 → ℝ) (hX : Continuous X) (A : GeometricExteriorCoordinate X) :
    Tendsto A.chart.symm (cobounded ℂ) (cocompact M) := by
  let e := A.chart
  have hh : Continuous (fun x => X x 2) := (continuous_apply 2).comp hX
  let : NoncompactSpace M := noncompact_of_exterior_height e A.target _ hh A.heightOffset A.height
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  have htail := homeomorphic_punctured_surface_connected_tails (0:PeriodTorus L₀) top
  have hesc := true_exterior_height_coordinate_escapes htail e A.target A.core _ hh A.heightOffset A.height
  let E := exteriorCoordinateComplexEnd e A.positive A.target A.core hesc
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cobounded ℂ) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_inv₀_cobounded,?_⟩
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with z hz
    exact inv_ne_zero (norm_pos_iff.mp hz)
  have h := E.from_zero.comp hi
  change Tendsto (fun z : ℂ => e.symm (z⁻¹)⁻¹) _ _ at h
  simpa only [inv_inv] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.geometric_exterior_inverse_escapes
