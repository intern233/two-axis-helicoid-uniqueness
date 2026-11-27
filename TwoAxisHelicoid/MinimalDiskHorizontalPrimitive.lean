import TwoAxisHelicoid.MinimalGraphClosedForm

namespace TwoAxisHelicoid
open Complex Metric Set Filter Topology
open scoped Topology ContDiff

/-- Local real C² primitives of a planar one-form on a ball give a
single C² primitive with the same differential on that entire ball. -/
theorem primitive_on_ball_of_local_c2 {form : ℂ → ℂ →L[ℝ] ℂ} {a : ℂ} {R : ℝ}
    (loc : ∀ z∈ball a R, ∃ H : ℂ → ℂ, ContDiffAt ℝ 2 H z ∧
      ∀ᶠ w in 𝓝 z, HasFDerivAt H (form w) w) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ 2 F (ball a R) ∧ ∀ z∈ball a R, HasFDerivAt F (form z) z := by
  have regular (z : ℂ) (hz : z∈ball a R) : ContDiffAt ℝ 1 form z ∧
      ∀ v w, fderiv ℝ form z v w=fderiv ℝ form z w v := by
    obtain ⟨H,sh,der⟩ := loc z hz
    have eqn : form =ᶠ[𝓝 z] fderiv ℝ H := der.mono fun _ h => h.fderiv.symm
    refine ⟨(sh.fderiv_right (m:=1) (by norm_num)).congr_of_eventuallyEq eqn,?_⟩
    intro v w
    rw [eqn.fderiv_eq (𝕜:=ℝ)]
    exact (sh.isSymmSndFDerivAt (by norm_num)).eq v w
  obtain ⟨F,dF⟩ := (convex_ball a R).exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_ball
    (fun z hz => (regular z hz).1.differentiableAt_one.differentiableWithinAt) (fun z hz => (regular z hz).2)
  refine ⟨F,fun z hz => ContDiffAt.contDiffWithinAt ?_,dF⟩
  apply (contDiffAt_succ_iff_hasFDerivAt (n:=1)).mpr
  exact ⟨form,⟨ball a R,isOpen_ball.mem_nhds hz,dF⟩,(regular z hz).1⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.primitive_on_ball_of_local_c2
