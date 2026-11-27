import TwoAxisHelicoid.ActualEmbeddedEnd
import TwoAxisHelicoid.ActualAreaVariationIndex
import TwoAxisHelicoid.HeightEndCurvature

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- The explicit primitive has an actual embedded end, with bounded
Gaussian curvature and arbitrarily large negative spaces for the second
derivative of its compact normal area integrals.  The height coordinate
is constructed from the actual primitive and covers its puncture. -/
theorem actual_primitive_embedded_end_actual_area_infinite_index
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    ∃ (K f : ℂ → ℂ) (R : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧ AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z) ∧
      (∀ ξ : ℂ, R ≤ ‖ξ‖ → actualComplexHeight t a c ht (K ξ) = ξ) ∧
      IsClosedEmbedding (fun ξ : {ξ : ℂ // R ≤ ‖ξ‖} => X (K ξ.1)) ∧
      (∀ ξ : ℂ, R ≤ ‖ξ‖ →
        |logGaussGaussianCurvature
          (fun z => I*((2*(a-1)/c : ℝ) : ℂ)*z+infinityCorrection f z) ξ| ≤
          (|2*(a-1)/c|+1)^2) ∧
      HasInfiniteCompactActualAreaIndexAtInfinity
        (fun ξ => verticalRotation I (X (K ξ)))
        (fun ξ => I*((2*(a-1)/c : ℝ) : ℂ)*ξ+infinityCorrection f ξ) := by
  obtain ⟨K,f,b,R₀,hK,hf,hf0,hKL,hcoord⟩ :=
    actual_primitive_analytic_height_end_coordinate ht ha hc hX
  have hα : 2*(a-1)/c ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_lt ha.2))) hc
  obtain ⟨A,_,hA⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (analytic_height_end_curvature_bounded (2*(a-1)/c) hf)
  obtain ⟨R,hR,hEmb⟩ := height_normalized_helicoidal_end_eventually_embedded
    (2*(a-1)/c) b (max R₀ A)
    (fun z hz => (hcoord z ((le_max_left _ _).trans_lt hz)).2.1)
    (fun z hz => (hcoord z ((le_max_left _ _).trans_lt hz)).2.2)
    (infinityCorrection_tendsto_zero hf hf0)
  refine ⟨K,f,R,hK,hf,hf0,hKL,
    (fun ξ hξ => (hcoord ξ ((le_max_left _ _).trans_lt (hR.trans_le hξ))).1),
    (vertical_quarter_turn_embedding_iff _).mp hEmb,
    (fun ξ hξ => hA ((le_max_right _ _).trans (hR.le.trans hξ))),?_⟩
  apply analytic_helicoid_actual_area_infinite_index hα hf hf0 (B := R₀+1)
  intro p hp
  exact (hcoord (planeComplex p)
    (by linarith [norm_le_planeComplex_norm p])).2.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_primitive_embedded_end_actual_area_infinite_index
