import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Complex.RealDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Bornology MeasureTheory
open scoped Topology

private noncomputable def exteriorPoint (x y : ℝ) : ℂ := x+I*y

@[simp] private theorem exteriorPoint_re (x y : ℝ) : (exteriorPoint x y).re = x := by
  simp [exteriorPoint,mul_re]

@[simp] private theorem exteriorPoint_im (x y : ℝ) : (exteriorPoint x y).im = y := by
  simp [exteriorPoint,mul_im]

private theorem exteriorPoint_vertical (x y : ℝ) : HasDerivAt (exteriorPoint x) I y := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 y := by simpa using! (ofRealCLM.hasDerivAt (x := y))
  change HasDerivAt (fun t : ℝ => (x:ℂ)+I*(t:ℂ)) I y
  simpa only [mul_one] using! (h.const_mul I).const_add (x : ℂ)

private theorem exteriorPoint_horizontal (x y : ℝ) : HasDerivAt (fun s => exteriorPoint s y) 1 x := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x := by simpa using! (ofRealCLM.hasDerivAt (x := x))
  exact h.add_const _

private theorem frequency_norm (z b : ℂ) : ‖exp (I*z)*b‖ = Real.exp (-z.im)*‖b‖ := by
  simp [Complex.norm_exp,Complex.mul_re]

/-- The total displacement on a vertical ray is bounded by the decaying
coefficient of the exponential differential, uniformly in the ray length. -/
private theorem vertical_primitive_bound {P B : ℂ → ℂ} {x Y δ : ℝ} (hY : 0 ≤ Y) (hδ : 0 ≤ δ)
    (hP : ∀ y ∈ Icc 0 Y, HasDerivAt P (exp (I*exteriorPoint x y)*B (exteriorPoint x y)) (exteriorPoint x y))
    (hB : ∀ y ∈ Icc 0 Y, ‖B (exteriorPoint x y)‖ ≤ δ) :
    dist (P (exteriorPoint x Y)) (P (x : ℂ)) ≤ δ := by
  let f := fun y => P (exteriorPoint x y)
  have hd (y) (hy : y ∈ Icc 0 Y) :
      HasDerivAt f (I • (exp (I*exteriorPoint x y)*B (exteriorPoint x y))) y :=
    (hP y hy).scomp y (exteriorPoint_vertical x y)
  have estimate := norm_sub_le_integral_of_norm_deriv_le_of_le (f := f) (B := fun y => δ*Real.exp (-y)) hY
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y ⟨hy.1.le,hy.2.le⟩).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall fun y hy => by
      have h : y ∈ Icc 0 Y := ⟨hy.1.le,hy.2.le⟩
      rw [(hd y h).deriv,norm_smul,norm_I,one_mul,frequency_norm,exteriorPoint_im,mul_comm δ]
      exact mul_le_mul_of_nonneg_left (hB y h) (Real.exp_pos _).le)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp] at estimate
  simp only [f,exteriorPoint,Complex.ofReal_zero,mul_zero,add_zero,neg_zero,Real.exp_zero] at estimate
  rw [dist_eq_norm_sub]
  exact estimate.trans (by nlinarith [mul_nonneg hδ (Real.exp_pos (-Y)).le])

/-- A horizontal bridge can cross the missing disk at sufficiently large
imaginary height. The exponentially small factor controls its whole length. -/
private theorem horizontal_primitive_bound {P B : ℂ → ℂ} {Y δ : ℝ} (x u : ℝ)
    (hP : ∀ v, HasDerivAt P (exp (I*exteriorPoint v Y)*B (exteriorPoint v Y)) (exteriorPoint v Y))
    (hB : ∀ v, ‖B (exteriorPoint v Y)‖ ≤ δ) :
    dist (P (exteriorPoint x Y)) (P (exteriorPoint u Y)) ≤ (Real.exp (-Y)*δ)*|x-u| := by
  let f := fun s => P (exteriorPoint s Y)
  have hd (s) : HasDerivAt f (exp (I*exteriorPoint s Y)*B (exteriorPoint s Y)) s := by
    change HasDerivAt (P ∘ (fun v : ℝ => exteriorPoint v Y)) _ s
    simpa only [one_smul] using! (hP s).scomp s (exteriorPoint_horizontal s Y)
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => by
      rw [frequency_norm,exteriorPoint_im]
      exact mul_le_mul_of_nonneg_left (hB s) (Real.exp_pos _).le)
    (mem_univ u) (mem_univ x)
  simpa only [dist_eq_norm_sub,Real.norm_eq_abs] using h

/-- For a single-valued primitive of exp(i z) times a term tending to zero
at infinity, both real tails converge to the same complex constant. -/
theorem exterior_oscillatory_primitive_common_limit {P B : ℂ → ℂ} (R₀ : ℝ)
    (hP : ∀ z : ℂ, R₀ < ‖z‖ → HasDerivAt P (exp (I*z)*B z) z)
    (hb : Tendsto B (cobounded ℂ) (𝓝 0)) :
    ∃ c : ℂ, Tendsto (fun x : ℝ => P (x : ℂ)) (cobounded ℝ) (𝓝 c) := by
  apply cauchy_map_iff_exists_tendsto.mp
  refine Metric.cauchy_iff.mpr ⟨inferInstance,?_⟩
  intro ε hε
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have small : ∀ᶠ z in cobounded ℂ, ‖B z‖ < δ := by
    simpa only [Metric.mem_ball,dist_zero_right] using hb.eventually (Metric.ball_mem_nhds 0 hδ)
  obtain ⟨S,_,hS⟩ := hasBasis_cobounded_norm.eventually_iff.mp small
  let R := max S (R₀+1)
  have hder {z : ℂ} (hz : R ≤ ‖z‖) := hP z ((lt_of_lt_of_le (by linarith : R₀ < R₀+1) (le_max_right S (R₀+1))).trans_le hz)
  have bound {z : ℂ} (hz : R ≤ ‖z‖) := (hS ((le_max_left _ _).trans hz)).le
  let U := {x : ℝ | R ≤ ‖x‖}
  have hU : U ∈ cobounded ℝ := hasBasis_cobounded_norm.mem_iff.mpr
    ⟨max R 1,trivial,fun x hx => show R ≤ ‖x‖ from (le_max_left R 1).trans hx⟩
  refine ⟨(fun x : ℝ => P (x : ℂ)) '' U,image_mem_map hU,?_⟩
  rintro _ ⟨x,hx,rfl⟩ _ ⟨u,hu,rfl⟩
  change R ≤ ‖x‖ at hx
  change R ≤ ‖u‖ at hu
  have normx (s v : ℝ) : ‖s‖ ≤ ‖exteriorPoint s v‖ := by
    simpa only [exteriorPoint_re,Real.norm_eq_abs] using Complex.abs_re_le_norm (exteriorPoint s v)
  have normy (s v : ℝ) : v ≤ ‖exteriorPoint s v‖ := (le_abs_self v).trans (by
    simpa only [exteriorPoint_im] using Complex.abs_im_le_norm (exteriorPoint s v))
  have est : ∀ᶠ Y : ℝ in atTop, dist (P (x : ℂ)) (P (u : ℂ)) ≤ δ+(Real.exp (-Y)*δ)*|x-u|+δ := by
    filter_upwards [eventually_ge_atTop (max R 0)] with Y hY
    have hy : 0 ≤ Y := (le_max_right _ _).trans hY
    have hr : R ≤ Y := (le_max_left _ _).trans hY
    have vx := vertical_primitive_bound hy hδ.le
      (fun v _ => hder (hx.trans (normx x v))) (fun v _ => bound (hx.trans (normx x v)))
    have vu := vertical_primitive_bound hy hδ.le
      (fun v _ => hder (hu.trans (normx u v))) (fun v _ => bound (hu.trans (normx u v)))
    have hh := horizontal_primitive_bound x u (fun s => hder (hr.trans (normy s Y)))
      (fun s => bound (hr.trans (normy s Y)))
    rw [dist_comm (P (exteriorPoint x Y))] at vx
    exact (dist_triangle4 _ _ _ _).trans (add_le_add (add_le_add vx hh) vu)
  have lim : Tendsto (fun Y : ℝ => δ+(Real.exp (-Y)*δ)*|x-u|+δ) atTop (𝓝 (δ+0+δ)) := by
    simpa only [zero_mul] using (((tendsto_const_nhds (x := δ)).add
      ((Real.tendsto_exp_neg_atTop_nhds_zero.mul_const δ).mul_const |x-u|)).add_const δ)
  exact (ge_of_tendsto lim est).trans_lt (by dsimp [δ]; linarith)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_oscillatory_primitive_common_limit
