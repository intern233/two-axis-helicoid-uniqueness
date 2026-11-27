import TwoAxisHelicoid.ChartAvoidingPaths
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 800000

theorem hasDerivAt_half_log_norm_sq {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hn : f x ≠ 0) :
    HasDerivAt (fun s => Real.log (‖f s‖^2)/2) (f'/f x).re x := by
  have hd := (hf.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).div_const 2
  convert hd using 1
  rw [Complex.div_re,Complex.inner,Complex.sq_norm]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

noncomputable def chartLogDerivative (g : X → ℂ) (p : X) (z : ℂ) : ℂ :=
  logDeriv (fun w : ℂ => g ((chartAt ℂ p).symm w)) z

theorem chartLogDerivative_continuousAt {A : HolomorphicCoefficientDisks X} {U : Set X}
    {g : X → ℂ}
    (hg : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      AnalyticAt ℂ (fun w : ℂ => g ((chartAt ℂ p).symm w)) z)
    (hn : ∀ x ∈ U, g x ≠ 0) (p : X) {z : ℂ}
    (hz : z ∈ ball (chartAt ℂ p p) (A.radius p)) (hU : (chartAt ℂ p).symm z ∈ U) :
    ContinuousAt (chartLogDerivative g p) z := by
  have ha := hg p z hz hU
  exact (ha.deriv.div ha (hn _ hU)).continuousAt

/-- The real part of a single-valued Gauss map's logarithmic differential
has the actual potential `(log ‖g‖²)/2` along every coordinate segment. -/
theorem logDerivative_segment_real_integral {A : HolomorphicCoefficientDisks X} {U : Set X}
    {g : X → ℂ}
    (hg : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      AnalyticAt ℂ (fun w : ℂ => g ((chartAt ℂ p).symm w)) z)
    (hn : ∀ x ∈ U, g x ≠ 0) (p : X) {x y : X}
    (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p)
    (hU : ∀ s : ℝ, s ∈ Icc 0 1 → (chartAt ℂ p).symm (chartSegment p x y s) ∈ U) :
    (∫ s : ℝ in 0..1,
      (chartAt ℂ p y-chartAt ℂ p x)*chartLogDerivative g p (chartSegment p x y s)).re =
      Real.log (‖g y‖^2)/2-Real.log (‖g x‖^2)/2 := by
  let k : ℝ → ℂ := fun s => g ((chartAt ℂ p).symm (chartSegment p x y s))
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => Real.log (‖k s‖^2)/2)
        (((chartAt ℂ p y-chartAt ℂ p x)*chartLogDerivative g p (chartSegment p x y s)).re) s := by
    have ha := hg p _ (A.chartSegment_mem p hx hy hs) (hU s hs)
    have hk := ha.differentiableAt.hasDerivAt.scomp s
      (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ)
        (a := chartAt ℂ p x) (b := chartAt ℂ p y) (x := s))
    have hh := hasDerivAt_half_log_norm_sq hk (hn _ (hU s hs))
    convert hh using 1
    · rfl
    · simp only [chartLogDerivative,logDeriv_apply,smul_eq_mul,Function.comp_apply]
      congr 1
      ring
  have hi := segment_coefficient_integrable
    (fun p z hz hu => chartLogDerivative_continuousAt hg hn p hz hu) p hx hy hU
  have hri := And.intro (Complex.reCLM.integrable_comp hi.1) (Complex.reCLM.integrable_comp hi.2)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs)) hri
  have hInt := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ s : ℝ in 0..1,
    ((chartAt ℂ p y-chartAt ℂ p x)*chartLogDerivative g p (chartSegment p x y s)).re) =
    (∫ s : ℝ in 0..1,
      (chartAt ℂ p y-chartAt ℂ p x)*chartLogDerivative g p (chartSegment p x y s)).re at hInt
  rw [hInt] at he
  simpa only [k,chartSegment,AffineMap.lineMap_apply_one,AffineMap.lineMap_apply_zero,
    (chartAt ℂ p).left_inv hx.1,(chartAt ℂ p).left_inv hy.1] using! he

theorem AvoidingPath.logDerivative_real_integral {A : HolomorphicCoefficientDisks X} {U : Set X}
    {g : X → ℂ}
    (hg : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      AnalyticAt ℂ (fun w : ℂ => g ((chartAt ℂ p).symm w)) z)
    (hn : ∀ x ∈ U, g x ≠ 0) {x y : X} (c : A.AvoidingPath U x y) :
    (c.integral (chartLogDerivative g)).re = Real.log (‖g y‖^2)/2-Real.log (‖g x‖^2)/2 := by
  induction c with
  | refl x hx => simp only [integral,zero_re,sub_self]
  | step p x y hx hy hU => exact logDerivative_segment_real_integral hg hn p hx hy hU
  | trans c d hc hd =>
      simp only [integral,add_re,hc,hd]
      ring

/-- Actual closed-path real periods of `dg/g` vanish by single-valuedness.
No integer winding or zero-period hypothesis is assumed. -/
theorem chartLogDerivative_zero_real_periods {A : HolomorphicCoefficientDisks X} {U : Set X}
    {g : X → ℂ}
    (hg : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      AnalyticAt ℂ (fun w : ℂ => g ((chartAt ℂ p).symm w)) z)
    (hn : ∀ x ∈ U, g x ≠ 0) : A.ZeroRealAvoidingPeriods U (chartLogDerivative g) := by
  intro x c
  rw [c.logDerivative_real_integral hg hn,sub_self]

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.chartLogDerivative_zero_real_periods
