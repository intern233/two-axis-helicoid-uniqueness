import TwoAxisHelicoid.CompactParameterCOneIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace TwoAxisHelicoid
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

/-- A C³ germ at the origin has a global C³ representative equal
to it on a neighborhood. The cutoff is supported strictly inside
the region where the germ is already smooth. -/
theorem planar_cubic_germ_representative {f : ℝ × ℝ → ℝ} (sm : ContDiffAt ℝ 3 f 0) :
    ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ 3 g ∧ g =ᶠ[𝓝 0] f := by
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp (sm.eventually (by norm_num))
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨r/4,r/2,by positivity,by linarith⟩
  refine ⟨fun z => b z*f z,contDiff_iff_contDiffAt.mpr (fun z => ?_),?_⟩
  · by_cases hz : z∈tsupport b
    · rw [b.tsupport_eq] at hz
      exact b.contDiff.contDiffAt.mul (sub ((closedBall_subset_ball (show b.rOut<r by dsimp [b]; linarith)) hz))
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
      change b w=0 at hw
      simp [hw]
  · filter_upwards [b.eventuallyEq_one] with z hz
    change b z=1 at hz
    simp [hz]

/-- Taylor's integral remainder at a planar critical point is a C¹
field of bilinear forms evaluated on the actual displacement twice.
Its value at the critical point is one half of the Hessian. -/
theorem planar_critical_taylor_bilinear {f : ℝ × ℝ → ℝ}
    (sm : ContDiffAt ℝ 3 f 0) (critical : fderiv ℝ f 0=0) :
    ∃ Q : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ,
      ContDiff ℝ 1 Q ∧ Q 0=(1/2:ℝ) • fderiv ℝ (fderiv ℝ f) 0 ∧
      ∀ᶠ z in 𝓝 0, f z=f 0+Q z z z := by
  obtain ⟨g,sg,agree⟩ := planar_cubic_germ_representative sm
  let D := fderiv ℝ (fderiv ℝ g)
  let K := fun p : (ℝ × ℝ) × ℝ => (1-p.2) • D (p.2 • p.1)
  let Q := fun z : ℝ × ℝ => ∫ t in (0:ℝ)..1, K (z,t)
  have sd : ContDiff ℝ 1 D := (sg.fderiv_right (m:=2) (by norm_num)).fderiv_right (by norm_num)
  let A := (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ
  let : IsBoundedSMul ℝ A := .of_norm_smul_le (fun r v => ContinuousLinearMap.opNorm_smul_le r v)
  have scale : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => 1-p.2) := contDiff_const.sub contDiff_snd
  have sk : ContDiff ℝ 1 K := scale.smul (sd.comp (contDiff_snd.smul contDiff_fst))
  have moment : (∫ t in (0:ℝ)..1, 1-t)=(1/2:ℝ) := by
    rw [intervalIntegral.integral_sub (f:=fun _ : ℝ => (1:ℝ)) (g:=fun t : ℝ => t)
      (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const,integral_id]
    norm_num
  have dg : fderiv ℝ g 0=0 := (agree.fderiv_eq (𝕜:=ℝ)).trans critical
  refine ⟨Q,contDiff_one_compact_parameter_integral sk 0 1,?_,?_⟩
  · change (∫ t in (0:ℝ)..1, (1-t) • D (t • 0))=_
    simp only [smul_zero]
    rw [intervalIntegral.integral_smul_const (fun t : ℝ => 1-t) (D 0),moment]
    exact congrArg (fun B => (1/2:ℝ) • B) ((agree.fderiv (𝕜:=ℝ)).fderiv_eq (𝕜:=ℝ))
  · filter_upwards [agree] with z eq
    have cont : Continuous (fun t : ℝ => K (z,t)) := sk.continuous.comp (continuous_const.prodMk continuous_id)
    have cont' : Continuous (fun t : ℝ => K (z,t) z) := cont.clm_apply continuous_const
    have value : Q z z z=∫ t in (0:ℝ)..1, (1-t)*D (t • z) z z := by
      change (∫ t in (0:ℝ)..1, K (z,t)) z z=_
      rw [ContinuousLinearMap.intervalIntegral_apply (cont.intervalIntegrable _ _),
        ContinuousLinearMap.intervalIntegral_apply (cont'.intervalIntegrable _ _)]
      rfl
    have formula := map_add_eq_sum_add_integral_iteratedFDeriv (f:=g) (n:=1) (x:=0) (y:=z)
      (fun _ _ => sg.contDiffAt.of_le (by norm_num))
    rw [← eq,← agree.eq_of_nhds,value]
    simpa [D,Finset.sum_range_succ,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,iteratedFDeriv_two_apply,dg,
      smul_eq_mul] using formula

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planar_cubic_germ_representative
#print axioms TwoAxisHelicoid.planar_critical_taylor_bilinear
