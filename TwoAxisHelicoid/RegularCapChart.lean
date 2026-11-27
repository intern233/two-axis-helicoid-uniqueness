import TwoAxisHelicoid.CappedLocalImmersion
import TwoAxisHelicoid.ImmersionAtlas

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology ContDiff

/-- Transfer each genuine finite-point immersion chart through the
actual cap formula. The old chart is restricted away from the puncture. -/
theorem ambient_cap_regular_chart
    {M E : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X F : M → HelicoidTubeCoordinates} {p : M}
    (e : OpenPartialHomeomorph M E) (he : RegularImmersionChart X e)
    (hp : p ∉ e.source) {A H R : ℝ}
    (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hF : ∀ x ≠ p, F x = ambientPlaneCap A H (X x))
    (hflat : ∀ x ≠ p, R^2 < ambientRadiusSq (X x) → (X x).1.2 = 0) :
    RegularImmersionChart F e := by
  intro y hy
  have hne (z : E) (hz : z ∈ e.target) : e.symm z ≠ p := by
    intro hh
    exact hp (hh ▸ e.map_target hz)
  have hEq : F ∘ e.symm =ᶠ[𝓝 y] ambientPlaneCap A H ∘ (X ∘ e.symm) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact hF (e.symm z) (hne z hz)
  have hX := (he y hy).1
  refine ⟨((ambientPlaneCap_contDiff A H).contDiffAt.comp y hX).congr_of_eventuallyEq hEq,?_⟩
  rw [hEq.fderiv_eq]
  apply ambientPlaneCap_preserves_local_immersion (hX.differentiableAt (by simp))
    (he y hy).2 hR hA1 hAR hH
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact hflat (e.symm z) (hne z hz)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ambient_cap_regular_chart
