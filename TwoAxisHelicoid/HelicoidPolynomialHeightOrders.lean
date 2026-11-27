import TwoAxisHelicoid.HelicoidHeightPoleDegree
import TwoAxisHelicoid.PolynomialHeightMeromorphic

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- Polynomial growth of the spatial height in a compactifying
coordinate, with any exponent, forces both exact height orders.
The analytic primitive need only be holomorphic on the puncture. -/
theorem HasHelicoidC1End.polynomial_height_orders {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (cont : Continuous X)
    (E : PuncturedComplexEnd M) {H : ℂ → ℂ} {b : ℝ}
    (height : ∀ᶠ z in 𝓝[≠] (0:ℂ), (X (E.coord.symm z)).2=(H z).re+b)
    (diff : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ H z)
    (growth : ∃ N : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ), |(X (E.coord.symm z)).2|≤C/‖z‖^N) :
    MeromorphicAt H 0 ∧ meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ) ∧
      MeromorphicAt (deriv H) 0 ∧ meromorphicOrderAt (deriv H) 0=((-2:ℤ):WithTop ℤ) := by
  obtain ⟨N,C,hC,bd⟩ := growth
  obtain ⟨r,hr,near⟩ := Metric.mem_nhdsWithin_iff.mp (height.and (diff.and bd))
  let R := min r 1
  have pos : 0<R := lt_min hr zero_lt_one
  have good (z : ℂ) (nz : 0<‖z‖) (small : ‖z‖<R) := near
    (show z∈ball (0:ℂ) r ∩ {0}ᶜ from ⟨by rw [mem_ball,dist_zero_right]; exact small.trans_le (min_le_left _ _),
      norm_pos_iff.mp nz⟩)
  have mer := meromorphic_of_polynomial_real_height (H := H) pos (show 0<C+|b| by linarith [abs_nonneg b]) N
    (fun z nz small => (good z nz small).2.1) (fun z nz small => by
      obtain ⟨eq,_,h⟩ := good z nz small
      have p := pow_pos nz N
      have u : ‖z‖^N≤1 := pow_le_one₀ nz.le (small.le.trans (min_le_right _ _))
      rw [le_div_iff₀ p] at h ⊢
      calc
        |(H z).re| *‖z‖^N = |(X (E.coord.symm z)).2-b| *‖z‖^N := by rw [eq,add_sub_cancel_right]
        _ ≤ (|(X (E.coord.symm z)).2|+|b|)*‖z‖^N := mul_le_mul_of_nonneg_right (abs_sub _ _) p.le
        _ ≤ C+|b| := by nlinarith [mul_le_mul_of_nonneg_left u (abs_nonneg b)])
  exact ⟨mer,graph.meromorphic_height_orders cont E mer height⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.polynomial_height_orders
