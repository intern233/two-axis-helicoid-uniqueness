import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology InnerProductSpace Real MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def diskPoissonValue (b : ℂ → ℝ) (c : ℂ) (r : ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun z => poissonKernel c w z*b z) c r

/-- The harmonic extension of arbitrary continuous real boundary data
is analytic inside the disk as a real part of a holomorphic Cauchy
transform. No differentiability of the boundary data is used. -/
theorem disk_poisson_value_harmonic {c : ℂ} {r : ℝ} (rp : 0<r) {b : ℂ → ℝ}
    (cont : ContinuousOn b (sphere c r)) : HarmonicOnNhd (diskPoissonValue b c r) (ball c r) := by
  let B := fun z => (b z:ℂ)
  have cb : ContinuousOn B (sphere c r) := Complex.continuous_ofReal.comp_continuousOn cont
  let A := fun w => (2*π*I:ℂ)⁻¹ • ∮ z in C(c,r), (z-w)⁻¹ • B z
  let R : ℝ≥0 := ⟨r,rp.le⟩
  have series := hasFPowerSeriesOn_cauchy_integral (c:=c) (R:=R)
    (show CircleIntegrable B c R from cb.circleIntegrable rp.le) (show 0<R from rp)
  have formula (w : ℂ) (hw : w∈ball c r) :
      diskPoissonValue b c r w=(2*A w-Real.circleAverage B c r).re := by
    let Q := fun z : ℂ => ((z-c)/(z-w))*B z
    have wz : w∉sphere c r := fun wh => (mem_ball.mp hw).ne (mem_sphere.mp wh)
    have nz (z : ℂ) (hz : z∈sphere c r) : z-w≠0 := sub_ne_zero.mpr (ne_of_mem_of_not_mem hz wz)
    have cq : ContinuousOn Q (sphere c r) :=
      (((continuous_id.sub continuous_const).continuousOn.div (continuous_id.sub continuous_const).continuousOn nz).mul cb)
    have qa : Real.circleAverage Q c r=A w := by
      rw [Real.circleAverage_eq_circleIntegral rp.ne']
      apply congrArg ((2*π*I:ℂ)⁻¹ • ·)
      apply circleIntegral.integral_congr rp.le
      intro z hz
      change (z-c)⁻¹*((z-c)/(z-w)*B z)=(z-w)⁻¹*B z
      have zc : z-c≠0 := sub_ne_zero.mpr (fun eq => by subst z; exact rp.ne (by simpa using hz))
      field_simp
    let H := fun z : ℂ => (2:ℂ)*Q z-B z
    have ch : ContinuousOn H (sphere c r) := (continuousOn_const.mul cq).sub cb
    have avg : Real.circleAverage H c r=2*A w-Real.circleAverage B c r := by
      have two : CircleIntegrable (fun z => (2:ℂ) • Q z) c r := (cq.const_smul (2:ℂ)).circleIntegrable rp.le
      rw [show H=(fun z => (2:ℂ) • Q z-B z) from rfl,Real.circleAverage_fun_sub two (cb.circleIntegrable rp.le),
        Real.circleAverage_fun_smul,qa,smul_eq_mul]
    rw [← avg]
    unfold diskPoissonValue
    change _=Complex.reCLM (Real.circleAverage H c r)
    rw [← Complex.reCLM.circleAverage_comp_comm (ch.circleIntegrable rp.le)]
    apply Real.circleAverage_congr_sphere
    intro z hz
    rw [abs_of_pos rp] at hz
    have alg : (2:ℂ)*((z-c)/(z-w))-1=herglotzRieszKernel c w z := by
      rw [herglotzRieszKernel_def,show z-c-(w-c)=z-w by ring]
      field_simp [nz z hz]
      ring
    have eqH : H z=herglotzRieszKernel c w z*(b z:ℂ) := by
      change 2*((z-c)/(z-w)*B z)-B z=_
      rw [← alg]
      dsimp [B]
      ring
    change poissonKernel c w z*b z=(H z).re
    rw [eqH,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,poissonKernel_eq_re_herglotzRieszKernel]
    rfl
  intro w hw
  have aw : AnalyticAt ℂ A w := series.analyticAt_of_mem (by
    rw [← ENNReal.ofReal_coe_nnreal,Metric.eball_ofReal]
    exact hw)
  have complexAnalytic : AnalyticAt ℂ (fun z => 2*A z-Real.circleAverage B c r) w := (analyticAt_const.mul aw).sub analyticAt_const
  have harm := complexAnalytic.harmonicAt_re
  apply (harmonicAt_congr_nhds (f₂:=fun w => (2*A w-Real.circleAverage B c r).re) ?_).mpr harm
  filter_upwards [isOpen_ball.mem_nhds hw] with z hz using formula z hz

/-- The Poisson kernel is a positive probability density on every
interior circle average. -/
theorem disk_poisson_kernel_mass {c w : ℂ} {r : ℝ} (hw : w∈ball c r) :
    Real.circleAverage (poissonKernel c w) c r=1 := by
  have h : HarmonicOnNhd (fun _ : ℂ => (1:ℝ)) (closedBall c r) := fun _ _ => harmonicAt_const _
  have eq := h.circleAverage_poissonKernel_smul hw
  change Real.circleAverage (fun z => poissonKernel c w z * 1) c r=1 at eq
  simpa only [mul_one] using eq

theorem disk_poisson_kernel_nonnegative {c w z : ℂ} {r : ℝ} (hw : w∈ball c r) (hz : z∈sphere c r) :
    0≤poissonKernel c w z := by
  have sz : ‖z-c‖=r := by simpa [dist_eq_norm] using mem_sphere.mp hz
  have sw : ‖w-c‖<r := by simpa [dist_eq_norm] using mem_ball.mp hw
  rw [poissonKernel_def,sz]
  exact div_nonneg (sub_nonneg.mpr (sq_le_sq₀ (norm_nonneg _) (pos_of_mem_ball hw).le |>.2 sw.le)) (sq_nonneg _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disk_poisson_value_harmonic
