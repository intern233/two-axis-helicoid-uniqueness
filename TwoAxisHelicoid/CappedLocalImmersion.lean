import TwoAxisHelicoid.AmbientCapDifferential

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cap_normal_derivative_zero {X : E → HelicoidTubeCoordinates} {x : E}
    (hX : DifferentiableAt ℝ X x) (hflat : ∀ᶠ z in 𝓝 x, (X z).1.2 = 0) (v : E) :
    (fderiv ℝ X x v).1.2 = 0 := by
  have he : (capNormalCoordinate ∘ X) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := hflat
  have hd := (capNormalCoordinate.hasFDerivAt.comp x hX.hasFDerivAt).fderiv
  have hz : fderiv ℝ (capNormalCoordinate ∘ X) x = 0 := by
    rw [he.fderiv_eq]
    simp
  have hD : capNormalCoordinate.comp (fderiv ℝ X x) = 0 := hd.symm.trans hz
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) hD

/-- The global capping formula preserves every actual immersion chart.
At the joining cylinder its ambient derivative is the identity; outside,
the actual planar tangent condition and the cap derivative give rank two. -/
theorem ambientPlaneCap_preserves_local_immersion
    {X : E → HelicoidTubeCoordinates} {x : E} (hX : DifferentiableAt ℝ X x)
    (hXi : Function.Injective (fderiv ℝ X x)) {A H R : ℝ}
    (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hflat : ∀ᶠ z in 𝓝 x, R^2 < ambientRadiusSq (X z) → (X z).1.2 = 0) :
    Function.Injective (fderiv ℝ (ambientPlaneCap A H ∘ X) x) := by
  rw [fderiv_comp x ((ambientPlaneCap_contDiff A H).differentiable (by simp) (X x)) hX]
  by_cases hq : (X x).1.1^2+(X x).2^2 ≤ A
  · rw [ambientPlaneCap_fderiv_inner hq,ContinuousLinearMap.id_comp]
    exact hXi
  · have hradius : R^2 < ambientRadiusSq (X x) := by
      dsimp [ambientRadiusSq]
      nlinarith [sq_nonneg (X x).1.2,sq_nonneg R]
    have hc : ContinuousAt (fun z => ambientRadiusSq (X z)) x :=
      ambientRadiusSq_continuous.continuousAt.comp hX.continuousAt
    have hflatE : ∀ᶠ z in 𝓝 x, (X z).1.2 = 0 := by
      filter_upwards [hflat,hc.eventually (lt_mem_nhds hradius)] with z hz hzr
      exact hz hzr
    have hA0 : 0 ≤ A := by linarith
    have hH0 : 0 < H := by linarith
    have hker : ∀ v : E,
        ((fderiv ℝ (ambientPlaneCap A H) (X x)).comp (fderiv ℝ X x)) v = 0 → v = 0 := by
      intro v hv
      apply hXi
      rw [map_zero]
      exact ambientPlaneCap_fderiv_tangent_kernel hA0 hH0 (X x)
        (cap_normal_derivative_zero hX hflatE v) hv
    intro v w he
    apply sub_eq_zero.mp
    apply hker (v-w)
    rw [map_sub,he,sub_self]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ambientPlaneCap_preserves_local_immersion
