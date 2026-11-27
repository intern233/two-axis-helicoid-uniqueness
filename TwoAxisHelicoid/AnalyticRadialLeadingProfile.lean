import TwoAxisHelicoid.SmoothRadialDivision
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology Function
open scoped Topology ContDiff

/-- A nonzero real analytic germ in the plane is already nonzero as a
one-variable analytic germ on some straight line through the center. -/
theorem analytic_plane_germ_detected_on_line {f : ℂ → ℝ} {x : ℂ} (an : AnalyticAt ℝ f x)
    (nonzero : ¬ f =ᶠ[𝓝 x] 0) :
    ∃ v : ℂ, AnalyticAt ℝ (fun r : ℝ => f (x+r • v)) 0 ∧ ¬ (fun r : ℝ => f (x+r • v)) =ᶠ[𝓝 0] 0 := by
  obtain ⟨R,rp,valid⟩ := Metric.mem_nhds_iff.mp an.eventually_analyticAt
  have freq : ∃ᶠ y in 𝓝 x, f y≠0 := not_eventually.mp nonzero
  obtain ⟨y,hy,small⟩ := (freq.and_eventually (ball_mem_nhds x (half_pos rp))).exists
  let v := y-x
  have nv : ‖v‖<R/2 := by simpa only [mem_ball,dist_eq_norm,v] using small
  have line : AnalyticOnNhd ℝ (fun r : ℝ => f (x+r • v)) (Ioo (-2) 2) := by
    intro r hr
    have near : x+r • v∈ball x R := by
      rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hr.1.le,hr.2.le⟩) (norm_nonneg v)).trans_lt (by linarith)
    have scale : AnalyticAt ℝ (fun s : ℝ => s • v) r := (ContinuousLinearMap.toSpanSingleton ℝ v).analyticAt r
    have aff : AnalyticAt ℝ (fun s : ℝ => x+s • v) r := analyticAt_const.add scale
    have outer : AnalyticAt ℝ f (x+r • v) := valid near
    exact outer.comp (f := fun s : ℝ => x+s • v) aff
  refine ⟨v,line 0 (by constructor <;> norm_num),?_⟩
  intro zero
  have all := line.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo
    (by constructor <;> norm_num : (0:ℝ)∈Ioo (-2) 2) zero
  have yzero := all (by constructor <;> norm_num : (1:ℝ)∈Ioo (-2) 2)
  exact hy (by simpa [v] using yzero)

noncomputable def iteratedRadialQuotient : ℕ → (ℝ × ℂ → ℝ) → ℝ × ℂ → ℝ
  | 0,F => F
  | k+1,F => radialDifferenceQuotient (iteratedRadialQuotient k F)

private theorem iterated_radial_smooth {F : ℝ × ℂ → ℝ} (sm : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedRadialQuotient n F) := by
  induction n with
  | zero => exact sm
  | succ n ih => exact (smooth_radial_difference_quotient ih).1

private theorem iterated_radial_factor {F : ℝ × ℂ → ℝ} (sm : ContDiff ℝ ∞ F) (n : ℕ)
    (lower : ∀ k<n, ∀ v, iteratedRadialQuotient k F (0,v)=0) (r : ℝ) (v : ℂ) :
    F (r,v)=r^n*iteratedRadialQuotient n F (r,v) := by
  induction n with
  | zero => simp [iteratedRadialQuotient]
  | succ n ih =>
    have step := (smooth_radial_difference_quotient (iterated_radial_smooth sm n)).2 r v
    rw [lower n (Nat.lt_succ_self n),zero_add] at step
    calc
      F (r,v)=r^n*iteratedRadialQuotient n F (r,v) := ih (fun k hk => lower k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      _=r^(n+1)*iteratedRadialQuotient (n+1) F (r,v) := by rw [step,pow_succ,mul_assoc]; rfl

/-- Jointly smooth division in all planar directions isolates the first
nonzero homogeneous degree. Only analyticity on a single nonzero radial
germ is needed to guarantee termination. -/
theorem smooth_radial_leading_profile {f : ℂ → ℝ} {x : ℂ} (sm : ContDiff ℝ ∞ f)
    (zero : f x=0) (critical : fderiv ℝ f x=0) (an : AnalyticAt ℝ f x)
    (nonzero : ¬ f =ᶠ[𝓝 x] 0) :
    ∃ (n : ℕ) (H : ℝ × ℂ → ℝ), 2≤n ∧ ContDiff ℝ ∞ H ∧ (∃ v, H (0,v)≠0) ∧
      ∀ r v, f (x+r • v)=r^n*H (r,v) := by
  classical
  let F := fun p : ℝ × ℂ => f (x+p.1 • p.2)
  have sF : ContDiff ℝ ∞ F := sm.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))
  obtain ⟨v,analytic,visible⟩ := analytic_plane_germ_detected_on_line an nonzero
  let line := fun r : ℝ => f (x+r • v)
  let m := analyticOrderNatAt line 0
  obtain ⟨g,ag,nz,expansion⟩ := analytic.analyticOrderAt_ne_top.mp
    (show analyticOrderAt line 0≠⊤ from fun eq => visible (analyticOrderAt_eq_top.mp eq))
  have existsDegree : ∃ n : ℕ, ∃ w : ℂ, iteratedRadialQuotient n F (0,w)≠0 := by
    by_contra! none
    let Q := iteratedRadialQuotient (m+1) F
    have compare : g =ᶠ[𝓝[≠] (0:ℝ)] fun r => r*Q (r,v) := by
      filter_upwards [expansion.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr ne
      have eq := iterated_radial_factor sF (m+1) (fun k _ => none k) r v
      change line r=r^(m+1)*Q (r,v) at eq
      change line r=(r-0)^m • g r at hr
      simp only [sub_zero,smul_eq_mul] at hr
      apply mul_left_cancel₀ (pow_ne_zero m (show r≠0 from ne))
      simpa only [pow_succ,mul_assoc] using hr.symm.trans eq
    have cont : ContinuousAt (fun r : ℝ => r*Q (r,v)) 0 := continuousAt_id.mul
      ((iterated_radial_smooth sF (m+1)).continuous.continuousAt.comp (continuousAt_id.prodMk continuousAt_const))
    have eq := tendsto_nhds_unique_of_eventuallyEq ag.continuousAt.continuousWithinAt cont.continuousWithinAt compare
    exact nz (eq.trans (zero_mul _))
  let n := Nat.find existsDegree
  let H := iteratedRadialQuotient n F
  have lower : ∀ k<n, ∀ w : ℂ, iteratedRadialQuotient k F (0,w)=0 := by
    intro k hk w
    by_contra h
    exact Nat.find_min existsDegree hk ⟨w,h⟩
  have form := iterated_radial_factor sF n lower
  have sh := iterated_radial_smooth sF n
  obtain ⟨u,hu⟩ := Nat.find_spec existsDegree
  change H (0,u)≠0 at hu
  have radial (r : ℝ) : f (x+r • u)=r^n*H (r,u) := form r u
  have d0 : HasDerivAt (fun r : ℝ => f (x+r • u)) 0 0 := by
    have p := (hasDerivAt_id (0:ℝ)).smul_const u
    have a : x+(0:ℝ) • u=x := by simp
    have df : HasFDerivAt f (0 : ℂ →L[ℝ] ℝ) (x+(0:ℝ) • u) := by
      rw [a,← critical]
      exact (sm.differentiable (by norm_num) x).hasFDerivAt
    simpa only [zero_apply,Function.comp_def,id_eq] using df.comp_hasDerivAt 0 (p.const_add x)
  refine ⟨n,H,?_,sh,⟨u,hu⟩,form⟩
  by_contra! small
  rcases (by omega : n=0 ∨ n=1) with h|h
  · have power : (0:ℝ)^n=1 := by rw [h,pow_zero]
    exact hu (by simpa only [zero_smul,add_zero,zero,power,one_mul] using (radial 0).symm)
  · have dr : DifferentiableAt ℝ (fun r : ℝ => H (r,u)) 0 :=
      (sh.differentiable (by norm_num) _).comp 0 (differentiableAt_id.prodMk (differentiableAt_const u))
    have a := (hasDerivAt_id (0:ℝ)).mul dr.hasDerivAt
    have same : (fun r : ℝ => f (x+r • u))=(fun r : ℝ => r*H (r,u)) := by
      funext r
      have power : r^n=r := by rw [h,pow_one]
      simpa only [power] using radial r
    rw [same] at d0
    exact hu (by simpa [id_eq] using a.unique d0)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_radial_leading_profile
