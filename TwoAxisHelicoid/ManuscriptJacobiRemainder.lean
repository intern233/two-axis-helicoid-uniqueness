import TwoAxisHelicoid.CoerciveLocalRigidity

namespace TwoAxisHelicoid
open Filter Asymptotics
open scoped Topology

/-- The remainder expansion of Appendix D.4. It precedes the a priori
estimate: coercivity is needed only for the final isolated-zero conclusion. -/
theorem differentiable_jacobi_remainder_and_isolated_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {M : E → F} {L : E →L[ℝ] F}
    (linearization : HasFDerivAt M L 0) (origin : M 0=0) :
    let R := fun u => M u-L u
    (∀ u, M u=L u+R u) ∧
      ((fun u => ‖R u‖) =o[𝓝 (0:E)] (fun u : E => ‖u‖)) ∧
      ∀ C : ℝ, (∀ u, ‖u‖≤C*‖L u‖) → ∃ r>0, ∀ u, ‖u‖<r → M u=0 → u=0 := by
  refine ⟨fun u => ?_,?_,fun _ bound => differentiable_coercive_isolated_zero linearization origin bound⟩
  · change M u=L u+(M u-L u)
    abel
  · rw [isLittleO_norm_left,isLittleO_norm_right]
    simpa only [zero_add,origin,sub_zero] using (hasFDerivAt_iff_isLittleO_nhds_zero.mp linearization)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.differentiable_jacobi_remainder_and_isolated_zero
