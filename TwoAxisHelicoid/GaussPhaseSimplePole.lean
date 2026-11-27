import TwoAxisHelicoid.HeightPoleRayLog
import Mathlib.Analysis.Calculus.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- A bounded-modulus Gauss direction avoiding the radial meridian
on the actual center ruling forces a meromorphic logarithmic factor
to have a simple pole. The argument allows any winding integer. -/
theorem gauss_factor_simple_from_center_phase {p : ℝ → ℂ} {g H F : ℂ → ℂ} (n : ℤ)
    (lim : Tendsto p atTop (𝓝[≠] 0)) (hm : MeromorphicAt H 0) (fm : MeromorphicAt F 0)
    (ho : meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ)) (fac : ∀ᶠ z in 𝓝[≠] (0:ℂ), g z=z^n*exp (F z))
    (ray : ∀ᶠ t in atTop, ContinuousAt p t ∧ ContinuousAt H (p t) ∧ ContinuousAt F (p t) ∧
      |(H (p t)).re-t|≤1 ∧ (∀ a : ℝ, g (p t)≠(a:ℂ)*exp ((t:ℂ)*I)) ∧ 1/10≤‖g (p t)‖ ∧ ‖g (p t)‖≤10) :
    meromorphicOrderAt F 0=((-1:ℤ):WithTop ℤ) := by
  have bright : ∀ᶠ t in atTop, ContinuousAt p t ∧ ContinuousAt H (p t) ∧ 0<(H (p t)).re := by
    filter_upwards [ray,eventually_gt_atTop (2:ℝ)] with t h ht
    exact ⟨h.1,h.2.1,by linarith [(abs_le.mp h.2.2.2.1).1]⟩
  obtain ⟨J,lift⟩ := bounded_puncture_log_on_height_ray lim hm ho bright
  let D := fun t => F (p t)+(n:ℂ)*J t
  let θ := fun t => (D t).im-t
  have de : ∀ᶠ t in atTop, exp (D t)=g (p t) ∧ ContinuousAt θ t ∧ exp ((θ t:ℂ)*I)≠1 := by
    filter_upwards [ray,lift,lim.eventually fac] with t h l fa
    have expD : exp (D t)=g (p t) := by dsimp [D]; rw [exp_add,exp_int_mul,l.2.1,fa,mul_comm]
    have cd : ContinuousAt D t := (h.2.2.1.comp h.1).add (continuousAt_const.mul l.1)
    refine ⟨expD,(continuous_im.continuousAt.comp cd).sub continuousAt_id,?_⟩
    intro bad
    change exp ((((D t).im-t:ℝ):ℂ)*I)=1 at bad
    rw [ofReal_sub,sub_mul,exp_sub,div_eq_one_iff_eq (exp_ne_zero _)] at bad
    apply h.2.2.2.2.1 (Real.exp (D t).re)
    rw [← expD,ofReal_exp,← bad,← exp_add,re_add_im]
  obtain ⟨A,atA⟩ := eventually_atTop.mp de
  obtain ⟨B,bpos,angle⟩ := bounded_angle_avoiding_one (isPreconnected_Ici (a := A))
    (fun t ht => (atA t ht).2.1.continuousWithinAt) (fun t ht => (atA t ht).2.2)
  let K := B+|(n:ℝ)| * (3*Real.pi)
  have kpos : 0≤K := by dsimp [K]; positivity
  have bounds : ∀ᶠ t in atTop,
      |(F (p t)).im-t|≤K ∧ |(F (p t)).re|≤Real.log 10+|(n:ℝ)| * |Real.log ‖p t‖| := by
    filter_upwards [de,ray,lift,eventually_ge_atTop A] with t h r l ht
    have e := angle t ht
    have im : (D t).im=(F (p t)).im+(n:ℝ)*(J t).im := by simp [D,Complex.mul_im]
    have re : (D t).re=(F (p t)).re+(n:ℝ)*(J t).re := by simp [D,Complex.mul_re]
    have jd : Real.log ‖p t‖=(J t).re := by rw [← l.2.1,Complex.norm_exp,Real.log_exp]
    have modulus : |(D t).re|≤Real.log 10 := by
      obtain ⟨gl,gh⟩ := r.2.2.2.2.2
      rw [← h.1,Complex.norm_exp] at gl gh
      have a := Real.log_le_log (by norm_num : (0:ℝ)<1/10) gl
      have b := Real.log_le_log (Real.exp_pos _) gh
      rw [Real.log_exp,one_div,Real.log_inv] at a
      rw [Real.log_exp] at b
      exact abs_le.mpr ⟨a,b⟩
    constructor
    · change |(D t).im-t|≤B at e
      have combine : (F (p t)).im-t=((D t).im-t)+ -((n:ℝ)*(J t).im) := by rw [im]; ring
      rw [combine]
      exact (abs_add_le _ _).trans (add_le_add e (by rw [abs_neg,abs_mul]; exact mul_le_mul_of_nonneg_left l.2.2 (abs_nonneg _)))
    · have combine : (F (p t)).re=(D t).re+ -((n:ℝ)*(J t).re) := by rw [re]; ring
      rw [combine,jd]
      exact (abs_add_le _ _).trans (add_le_add modulus (by rw [abs_neg,abs_mul]))
  have esc : Tendsto (fun t => ‖F (p t)‖) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [bounds,eventually_ge_atTop (b+K)] with t h ht
    have low := (abs_le.mp h.1).1
    exact (show b≤(F (p t)).im by linarith).trans ((le_abs_self _).trans (abs_im_le_norm _))
  obtain ⟨C,rad⟩ := simple_pole_norm_times_radius_bounded hm ho
  apply meromorphic_order_simple_of_ray lim fm esc
  refine ⟨(Real.log 10+K+1)+|(n:ℝ)|+C,?_⟩
  filter_upwards [bounds,ray,lim.eventually rad,lim.eventually self_mem_nhdsWithin,
    lim.eventually (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one)),eventually_ge_atTop (0:ℝ)] with t h r e nz sm ht
  let s := ‖p t‖
  have pos : 0<s := norm_pos_iff.mpr nz
  have one : s≤1 := (show ‖p t‖<1 by simpa only [mem_ball,dist_zero_right] using sm).le
  have logBound : s*|Real.log s|≤1 := by
    rw [abs_of_nonpos (Real.log_nonpos pos.le one)]
    calc
      _ ≤ s*s⁻¹ := mul_le_mul_of_nonneg_left (by linarith [Real.neg_inv_le_log pos.le]) pos.le
      _ = 1 := mul_inv_cancel₀ pos.ne'
  have phase : |(F (p t)).im|≤K+t := by
    have h' := abs_add_le ((F (p t)).im-t) t
    rw [sub_add_cancel,abs_of_nonneg ht] at h'
    exact h'.trans (add_le_add h.1 (le_refl t))
  have time : t≤‖H (p t)‖+1 := by linarith [(abs_le.mp r.2.2.2.1).1,(le_abs_self (H (p t)).re).trans (abs_re_le_norm _)]
  have magnitude := (norm_le_abs_re_add_abs_im (F (p t))).trans (add_le_add h.2 phase)
  have cpos : 0≤Real.log 10+K+1 := by positivity
  calc
    _ ≤ s*(Real.log 10+|(n:ℝ)| * |Real.log s|+(K+(‖H (p t)‖+1))) :=
      mul_le_mul_of_nonneg_left (magnitude.trans (by linarith)) pos.le
    _ = s*(Real.log 10+K+1)+|(n:ℝ)| * (s*|Real.log s|)+s*‖H (p t)‖ := by ring
    _ ≤ _ := by
      have a := mul_le_mul_of_nonneg_right one cpos
      have b := mul_le_mul_of_nonneg_left logBound (abs_nonneg (n:ℝ))
      change s*‖H (p t)‖≤C at e
      linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.gauss_factor_simple_from_center_phase
