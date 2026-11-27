import TwoAxisHelicoid.UnivalentAnalyticRegularity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.CauchyIntegral

namespace TwoAxisHelicoid
open Complex Set Filter Function Metric Topology
open scoped Topology

/-- Normalizations used in the blow-up argument for univalent
coordinates. Both jets refer to derivatives in the disk coordinate. -/
structure UnivalentRescaledDisk (F : ℂ → ℂ) (R : ℝ) : Prop where
  analytic : AnalyticOnNhd ℂ F (ball 0 R)
  injective : InjOn F (ball 0 R)
  origin : F 0=0
  first : deriv F 0=1
  second : deriv (deriv F) 0=1
  estimate : ∀ w∈ball 0 R, ‖deriv (deriv F) w‖≤2*‖deriv F w‖

/-- Maximize distance to the boundary times the logarithmic
derivative on a smaller closed disk, then translate and rescale.
A large value at the center supplies an arbitrarily large normalized
coordinate disk with uniform logarithmic derivative. -/
theorem rescale_large_univalent_jet {f : ℂ → ℂ} (hol : AnalyticOnNhd ℂ f (ball 0 1))
    (inj : InjOn f (ball 0 1)) {R : ℝ} (rp : 0<R)
    (large : 4*R<‖deriv (deriv f) 0 / deriv f 0‖) :
    ∃ F : ℂ → ℂ, UnivalentRescaledDisk F R := by
  let P := fun z => deriv (deriv f) z / deriv f z
  have reg (z : ℂ) (hz : z∈ball (0:ℂ) 1) := univalent_analytic_deriv_ne_zero isOpen_ball hol inj hz
  let B := closedBall (0:ℂ) (1/2:ℝ)
  have sub : B⊆ball (0:ℂ) 1 := closedBall_subset_ball (by norm_num)
  let weight := fun z : ℂ => (1/2-‖z‖)*‖P z‖
  have cp : ContinuousOn P B := fun z hz =>
    (((hol z (sub hz)).deriv.deriv.div (hol z (sub hz)).deriv (reg z (sub hz))).continuousAt.continuousWithinAt)
  have cw : ContinuousOn weight B := (continuous_const.sub continuous_norm).continuousOn.mul cp.norm
  have zeroB : (0:ℂ)∈B := mem_closedBall_self (by norm_num)
  obtain ⟨a,ha,mx⟩ := (isCompact_closedBall (0:ℂ) (1/2:ℝ)).exists_isMaxOn ⟨0,zeroB⟩ cw
  let δ := 1/2-‖a‖
  have scale : 2*R<δ*‖P a‖ := by
    have h : weight 0≤weight a := mx zeroB
    simp only [weight,norm_zero,sub_zero] at h
    change 4*R<‖P 0‖ at large
    dsimp [δ]
    linarith
  have dp : 0<δ := pos_of_mul_pos_left ((by positivity : 0≤2*R).trans_lt scale) (norm_nonneg _)
  have nz : P a≠0 := norm_pos_iff.mp (pos_of_mul_pos_right ((by positivity : 0≤2*R).trans_lt scale) dp.le)
  let s := (P a)⁻¹
  let h := fun z : ℂ => a+s*z
  let F := fun z : ℂ => (f (h z)-f a)/(s*deriv f a)
  have sn : s≠0 := inv_ne_zero nz
  have den := mul_ne_zero sn (reg a (sub ha))
  have radius (z : ℂ) (hz : z∈ball (0:ℂ) R) : ‖s*z‖<δ/2 := by
    rw [norm_mul,show ‖s‖=‖P a‖⁻¹ from norm_inv _,← div_eq_inv_mul]
    apply (div_lt_iff₀ (norm_pos_iff.mpr nz)).mpr
    nlinarith [mem_ball_zero_iff.mp hz]
  have inner (z : ℂ) (hz : z∈ball (0:ℂ) R) : ‖h z‖<‖a‖+δ/2 :=
    (norm_add_le a (s*z)).trans_lt (by linarith [radius z hz])
  have nearB (z : ℂ) (hz : z∈ball (0:ℂ) R) : h z∈B := by
    apply mem_closedBall_zero_iff.mpr
    have := inner z hz
    dsimp [δ] at *
    linarith
  have pre (z : ℂ) (hz : z∈ball (0:ℂ) R) : ‖P (h z)‖≤2*‖P a‖ := by
    have w : (1/2-‖h z‖)*‖P (h z)‖≤δ*‖P a‖ := mx (nearB z hz)
    have hh := inner z hz
    have gap : δ/2≤1/2-‖h z‖ := by dsimp [δ] at *; linarith
    have bound := (mul_le_mul_of_nonneg_right gap (norm_nonneg (P (h z)))).trans w
    nlinarith [mul_le_mul_iff_right₀ dp |>.mp (show δ*‖P (h z)‖≤δ*(2*‖P a‖) by linarith)]
  have da (z : ℂ) : HasDerivAt h s z := by simpa [h] using ((hasDerivAt_id z).const_mul s).const_add a
  have af (z : ℂ) (hz : z∈ball (0:ℂ) R) : AnalyticAt ℂ F z :=
    (((hol _ (sub (nearB z hz))).comp (analyticAt_const.add (analyticAt_const.mul analyticAt_id))).sub analyticAt_const).div_const
  have d1 (z : ℂ) (hz : z∈ball (0:ℂ) R) : deriv F z=deriv f (h z)*s/(s*deriv f a) :=
    (((hol _ (sub (nearB z hz))).differentiableAt.hasDerivAt.comp z (da z)).sub_const _ |>.div_const _).deriv
  have d2 (z : ℂ) (hz : z∈ball (0:ℂ) R) : deriv (deriv F) z=deriv (deriv f) (h z)*s*s/(s*deriv f a) := by
    have germ : deriv F =ᶠ[𝓝 z] fun w => deriv f (h w)*s/(s*deriv f a) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using d1 w hw
    exact germ.deriv_eq.trans (((((hol _ (sub (nearB z hz))).deriv.differentiableAt.hasDerivAt.comp z
      (da z)).mul_const s).div_const _).deriv)
  have h0 : h 0=a := by simp [h]
  have zero := mem_ball_self (x:=(0:ℂ)) rp
  refine ⟨F,af,?_,by simp [F,h0],?_,?_,?_⟩
  · intro x hx y hy eq
    change (f (h x)-f a)/(s*deriv f a)=(f (h y)-f a)/(s*deriv f a) at eq
    have same := inj (sub (nearB x hx)) (sub (nearB y hy)) (sub_left_inj.mp ((div_left_inj' den).mp eq))
    exact mul_left_cancel₀ sn (add_left_cancel same)
  · rw [d1 0 zero,h0,mul_comm,div_self den]
  · rw [d2 0 zero,h0,div_eq_one_iff_eq den]
    have iden : s*deriv (deriv f) a=deriv f a := by
      have hP : P a*deriv f a=deriv (deriv f) a := div_mul_cancel₀ _ (reg a (sub ha))
      rw [← hP,← mul_assoc,show s*P a=1 from inv_mul_cancel₀ nz,one_mul]
    rw [mul_comm (deriv (deriv f) a) s,iden,mul_comm]
  · intro z hz
    rw [d2 z hz,d1 z hz,norm_div,norm_div,norm_mul,norm_mul,norm_mul]
    have regZ := norm_pos_iff.mpr (reg _ (sub (nearB z hz)))
    have hP := pre z hz
    change ‖deriv (deriv f) (h z)/deriv f (h z)‖≤2*‖P a‖ at hP
    rw [norm_div,div_le_iff₀ regZ] at hP
    have cb : ‖deriv (deriv f) (h z)‖*‖s‖≤2*‖deriv f (h z)‖ := by
      rw [show ‖s‖=‖P a‖⁻¹ from norm_inv _,← div_eq_mul_inv,div_le_iff₀ (norm_pos_iff.mpr nz)]
      linarith only [hP]
    rw [norm_mul]
    have denPos := mul_pos (norm_pos_iff.mpr sn) (norm_pos_iff.mpr (reg a (sub ha)))
    have num := mul_le_mul_of_nonneg_right cb (norm_nonneg s)
    calc
      _ ≤ (2*‖deriv f (h z)‖*‖s‖)/(‖s‖*‖deriv f a‖) := div_le_div_of_nonneg_right num denPos.le
      _ = _ := by ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rescale_large_univalent_jet
