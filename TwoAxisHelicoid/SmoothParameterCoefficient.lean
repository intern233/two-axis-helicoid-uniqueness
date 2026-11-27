module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section

namespace TwoAxisHelicoid
open Complex Metric Set Filter Topology
open scoped ContDiff NNReal BoundedContinuousFunction

/-- A compact coefficient restricted to the translated spatial slice at a fixed
real parameter. The target norm is the supremum over the entire plane. -/
@[expose] noncomputable def compactParameterTrace (f : ℝ × ℂ → ℝ) (s : Continuous f)
    (h : HasCompactSupport f) (x : ℝ × ℂ) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => f (x.1,z+x.2))
    (s.comp (continuous_const.prodMk (continuous_id.add continuous_const)))
    (h.exists_bound_of_continuous s).choose (fun z => (h.exists_bound_of_continuous s).choose_spec (x.1,z+x.2))

private theorem trace_taylor {f : ℝ × ℂ → ℝ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f) :
    ∃ L : ℝ≥0, ∀ z t : ℝ × ℂ, ‖f (z+t)-f z-fderiv ℝ f z t‖≤(L:ℝ)*‖t‖^2 := by
  have sd : ContDiff ℝ ∞ (fderiv ℝ f) := s.fderiv_right (by simp)
  obtain ⟨L,lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (h.fderiv ℝ) sd (by simp)
  refine ⟨L,fun z t => ?_⟩
  have bd (y : ℝ × ℂ) (hy : y∈closedBall z ‖t‖) : ‖fderiv ℝ f y-fderiv ℝ f z‖ ≤ (L:ℝ)*‖t‖ := by
    exact (lip.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using mem_closedBall.mp hy) L.coe_nonneg)
  have est := (convex_closedBall z ‖t‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => s.differentiable (by simp) y) bd (mem_closedBall_self (norm_nonneg t))
    (show z+t∈closedBall z ‖t‖ by simp [mem_closedBall,dist_eq_norm])
  simpa [pow_two,mul_assoc] using est

private theorem trace_direction {f : ℝ × ℂ → ℝ} (s : ContDiff ℝ ∞ f) (d : ℝ × ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ f z d) :=
  (s.fderiv_right (by simp)).clm_apply contDiff_const

private noncomputable def traceDifferential {f : ℝ × ℂ → ℝ}
    (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f) (t : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] (ℂ →ᵇ ℝ) :=
  let J := fun d : ℝ × ℂ => compactParameterTrace _ (trace_direction s d).continuous (h.fderiv_apply ℝ d) t
  (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight (J (1,0)) +
    (reCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℂ)).smulRight (J (0,1)) +
    (imCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℂ)).smulRight (J (0,I))

private theorem traceDifferential_apply {f : ℝ × ℂ → ℝ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f)
    (t d : ℝ × ℂ) (z : ℂ) : traceDifferential s h t d z = fderiv ℝ f (t.1,z+t.2) d := by
  let L := fderiv ℝ f (t.1,z+t.2)
  change d.1*L (1,0)+d.2.re*L (0,1)+d.2.im*L (0,I)=L d
  have split : d=d.1 • ((1,0):ℝ × ℂ)+d.2.re • (0,(1:ℂ))+d.2.im • (0,I) := by
    apply Prod.ext <;> simp
  conv_rhs => rw [split]
  simp only [map_add,map_smul,smul_eq_mul]

private theorem hasFDerivAt_trace {f : ℝ × ℂ → ℝ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f)
    (t : ℝ × ℂ) : HasFDerivAt (compactParameterTrace f s.continuous h) (traceDifferential s h t) t := by
  obtain ⟨L,est⟩ := trace_taylor s h
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro c hc
  have lp : 0<(L:ℝ)+1 := by positivity
  filter_upwards [Metric.ball_mem_nhds t (div_pos hc lp)] with y hy
  have sm : ‖y-t‖<c/((L:ℝ)+1) := by simpa only [mem_ball,dist_eq_norm] using hy
  have prod : (L:ℝ)*‖y-t‖≤c := by
    have x := (lt_div_iff₀ lp).mp sm
    nlinarith [norm_nonneg (y-t)]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hc.le (norm_nonneg _))).mpr
  intro z
  change ‖f (y.1,z+y.2)-f (t.1,z+t.2)-traceDifferential s h t (y-t) z‖≤_
  rw [traceDifferential_apply]
  have e := est (t.1,z+t.2) (y-t)
  have ident : (t.1,z+t.2)+(y-t)=(y.1,z+y.2) := by apply Prod.ext <;> dsimp <;> abel
  rw [ident] at e
  exact e.trans (by simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_right prod (norm_nonneg (y-t)))

theorem smooth_compactParameterTrace {f : ℝ × ℂ → ℝ} (s : ContDiff ℝ ∞ f) (h : HasCompactSupport f) :
    ContDiff ℝ ∞ (compactParameterTrace f s.continuous h) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n unused
  clear unused
  induction n generalizing f with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun t => (hasFDerivAt_trace s h t).continuousAt)
  | succ n ih =>
    rw [Nat.cast_succ]
    apply contDiff_succ_iff_fderiv.mpr
    have df : fderiv ℝ (compactParameterTrace f s.continuous h)=traceDifferential s h :=
      funext fun t => (hasFDerivAt_trace s h t).fderiv
    refine ⟨fun t => (hasFDerivAt_trace s h t).differentiableAt,?_,?_⟩
    · simp
    · rw [df]
      exact ((contDiff_const.smulRight (ih (trace_direction s (1,0)) (h.fderiv_apply ℝ (1,0)))).add
        (contDiff_const.smulRight (ih (trace_direction s (0,1)) (h.fderiv_apply ℝ (0,1))))).add
        (contDiff_const.smulRight (ih (trace_direction s (0,I)) (h.fderiv_apply ℝ (0,I))))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_compactParameterTrace
