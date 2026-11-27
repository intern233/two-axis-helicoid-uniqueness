import TwoAxisHelicoid.UnivalentDiskJetBound

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function
open scoped Topology

/-- The universal unit-disk estimate in a disk of arbitrary radius. -/
theorem univalent_center_jet_on_ball {C : ℝ}
    (univBound : ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 1) → InjOn g (ball 0 1) →
      ‖deriv (deriv g) 0/deriv g 0‖≤C)
    {f : ℂ → ℂ} {a : ℂ} {r : ℝ} (rp : 0<r) (hol : AnalyticOnNhd ℂ f (ball a r)) (inj : InjOn f (ball a r)) :
    ‖deriv (deriv f) a‖≤(C/r)*‖deriv f a‖ := by
  let h := fun z : ℂ => a+(r:ℂ)*z
  let g := f ∘ h
  have dom (z : ℂ) (hz : z∈ball (0:ℂ) 1) : h z∈ball a r := by
    rw [mem_ball,dist_eq_norm]
    simp only [h,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_of_nonneg rp.le]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hz) rp).trans_eq (mul_one _)
  have rn := Complex.ofReal_ne_zero.mpr rp.ne'
  have gi : InjOn g (ball 0 1) := fun x hx y hy eq => mul_left_cancel₀ rn (add_left_cancel (inj (dom x hx) (dom y hy) eq))
  have gh : AnalyticOnNhd ℂ g (ball 0 1) := fun z hz =>
    (hol _ (dom z hz)).comp (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
  have d (z : ℂ) : HasDerivAt h (r:ℂ) z := by simpa [h] using ((hasDerivAt_id z).const_mul (r:ℂ)).const_add a
  have first (z : ℂ) (hz : z∈ball (0:ℂ) 1) : deriv g z=deriv f (h z)*(r:ℂ) :=
    ((hol _ (dom z hz)).differentiableAt.hasDerivAt.comp z (d z)).deriv
  have z0 : (0:ℂ)∈ball 0 (1:ℝ) := mem_ball_self one_pos
  have germ : deriv g =ᶠ[𝓝 (0:ℂ)] fun z => deriv f (h z)*(r:ℂ) := by
    filter_upwards [ball_mem_nhds (0:ℂ) one_pos] with z hz using first z hz
  have h0 : h 0=a := by simp [h]
  have second := germ.deriv_eq.trans ((((hol _ (dom 0 z0)).deriv.differentiableAt.hasDerivAt.comp 0 (d 0)).mul_const (r:ℂ)).deriv)
  have v := univBound g gh gi
  rw [second,first 0 z0,h0,norm_div,norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg rp.le] at v
  have reg := norm_pos_iff.mpr (univalent_analytic_deriv_ne_zero isOpen_ball hol inj (mem_ball_self rp))
  rw [div_le_iff₀ (mul_pos reg rp)] at v
  have v' : ‖deriv (deriv f) a‖*r≤C*‖deriv f a‖ :=
    (mul_le_mul_iff_left₀ rp).mp (by linarith only [v])
  have h' := (le_div_iff₀ rp).mpr v'
  convert h' using 1
  ring

/-- Uniform propagation between arbitrary two points of the inner disk,
using the true value and derivative at just one of them. -/
theorem univalent_disk_values_from_nearby_jet : ∃ C : ℝ, 0<C ∧
    ∀ (f : ℂ → ℂ) (c : ℂ) (r : ℝ), 0<r →
      AnalyticOnNhd ℂ f (ball c (4*r)) → InjOn f (ball c (4*r)) →
      ∀ a∈ball c r, ∀ z∈ball c r,
        ‖f z‖≤‖f a‖+‖deriv f a‖*Real.exp (2*C)*(2*r) := by
  obtain ⟨C,cp,univBound⟩ := univalent_unit_disk_jet_bound
  refine ⟨C,cp,?_⟩
  intro f c r rp hol inj a ha z hz
  have nearW (w : ℂ) (hw : w∈ball a (2*r)) : ball w r⊆ball c (4*r) := by
    intro u hu
    have h1 := dist_triangle u w a
    have h2 := dist_triangle u a c
    apply mem_ball.mpr
    linarith [mem_ball.mp hu,mem_ball.mp hw,mem_ball.mp ha]
  have sub : ball a (2*r)⊆ball c (4*r) := fun w hw => nearW w hw (mem_ball_self rp)
  have zr : z∈ball a (2*r) := mem_ball.mpr (by linarith [dist_triangle_right z a c,mem_ball.mp hz,mem_ball.mp ha])
  have v := holomorphic_value_growth (div_nonneg cp.le rp.le) (hol.mono sub)
    (fun w hw => univalent_center_jet_on_ball univBound rp (hol.mono (nearW w hw)) (inj.mono (nearW w hw))) zr
  rwa [show C/r*(2*r)=2*C by field_simp] at v

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.univalent_disk_values_from_nearby_jet
