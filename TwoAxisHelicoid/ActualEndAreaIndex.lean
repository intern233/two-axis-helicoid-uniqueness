import TwoAxisHelicoid.ActualHeightEndCoordinate
import TwoAxisHelicoid.CoordinateAreaIndex

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

/-- The explicitly reconstructed spatial primitive has arbitrarily large
negative compact normal-area Hessian test spaces in its genuine end chart.
This conclusion uses the actual map, not an independently postulated
logarithmic Gauss function or a separate end-chart hypothesis. -/
theorem actual_primitive_end_coordinate_area_infinite_index
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    ∃ (K f : ℂ → ℂ) (R₀ : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧ AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z) ∧
      (∀ ξ : ℂ, R₀ < ‖ξ‖ → actualComplexHeight t a c ht (K ξ) = ξ) ∧
      HasInfiniteCompactCoordinateAreaIndexAtInfinity (fun ξ => verticalRotation I (X (K ξ)))
        (fun ξ => I*((2*(a-1)/c : ℝ) : ℂ)*ξ+infinityCorrection f ξ) := by
  obtain ⟨K,f,b,R₀,hK,hf,hf0,hKL,hcoord⟩ :=
    actual_primitive_analytic_height_end_coordinate ht ha hc hX
  have hα : 2*(a-1)/c ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_lt ha.2))) hc
  refine ⟨K,f,R₀,hK,hf,hf0,hKL,(fun ξ hξ => (hcoord ξ hξ).1),?_⟩
  apply analytic_helicoid_actual_coordinate_area_infinite_index hα hf hf0 (B := R₀+1)
  intro p hp
  exact (hcoord (planeComplex p)
    (by linarith [norm_le_planeComplex_norm p])).2.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_primitive_end_coordinate_area_infinite_index
