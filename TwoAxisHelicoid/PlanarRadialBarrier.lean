import TwoAxisHelicoid.LocalMinimumLaplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set Metric Topology InnerProductSpace Laplacian
open scoped Topology InnerProductSpace

private noncomputable def radialSquared (c z : ℂ) : ℝ := (z.re-c.re)^2+(z.im-c.im)^2

private theorem radialSquared_dist (c z : ℂ) : radialSquared c z = dist z c^2 := by
  rw [dist_eq_norm,← Complex.normSq_eq_norm_sq]
  simp only [radialSquared,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,pow_two]

noncomputable def planarRadialBarrier (c : ℂ) (k r : ℝ) (z : ℂ) : ℝ :=
  Real.exp (-k*radialSquared c z)-Real.exp (-k*r^2)

theorem planarRadialBarrier_value (c z : ℂ) (k r : ℝ) :
    planarRadialBarrier c k r z = Real.exp (-k*dist z c^2)-Real.exp (-k*r^2) := by
  rw [planarRadialBarrier,radialSquared_dist]

theorem planarRadialBarrier_analytic (c z : ℂ) (k r : ℝ) : AnalyticAt ℝ (planarRadialBarrier c k r) z := by
  have hsq := (((reCLM.analyticAt z).sub (analyticAt_const (v := c.re))).pow 2).add
    (((imCLM.analyticAt z).sub (analyticAt_const (v := c.im))).pow 2)
  exact (analyticAt_rexp.comp (analyticAt_const.mul hsq)).sub analyticAt_const

private theorem radial_line_derivatives (c z v : ℂ) (k r : ℝ) :
    let B := fun s : ℝ => planarRadialBarrier c k r (z+s • v)
    let d := (z.re-c.re)*v.re+(z.im-c.im)*v.im
    let e := Real.exp (-k*radialSquared c z)
    deriv B 0 = -2*k*d*e ∧ deriv (deriv B) 0 = (4*k^2*d^2-2*k*(v.re^2+v.im^2))*e := by
  let q := fun t : ℝ => z+t • v
  let a := fun t : ℝ => (q t).re-c.re
  let b := fun t : ℝ => (q t).im-c.im
  let d := fun t : ℝ => a t*v.re+b t*v.im
  let e := fun t : ℝ => Real.exp (-k*radialSquared c (q t))
  let B := fun t : ℝ => planarRadialBarrier c k r (q t)
  have dq (t : ℝ) : HasDerivAt q v t := by simpa only [id_eq,one_smul] using! ((hasDerivAt_id t).smul_const v).const_add z
  have da (t : ℝ) : HasDerivAt a v.re t := (reCLM.hasFDerivAt.comp_hasDerivAt t (dq t)).sub_const c.re
  have db (t : ℝ) : HasDerivAt b v.im t := (imCLM.hasFDerivAt.comp_hasDerivAt t (dq t)).sub_const c.im
  have ds (t : ℝ) : HasDerivAt (fun s => radialSquared c (q s)) (2*d t) t := by
    have hh := ((da t).pow 2).add ((db t).pow 2)
    change HasDerivAt (fun s => radialSquared c (q s)) _ t at hh
    convert hh using 1
    change 2*(a t*v.re+b t*v.im) = _
    ring
  have de (t : ℝ) : HasDerivAt e (-2*k*d t*e t) t := by
    convert ((ds t).const_mul (-k)).exp using 1
    dsimp [e]
    ring
  have dd (t : ℝ) : HasDerivAt d (v.re^2+v.im^2) t := by
    convert ((da t).mul_const v.re).add ((db t).mul_const v.im) using 1
    ring
  have dB : deriv B = fun t => -2*k*d t*e t := funext fun t => ((de t).sub_const _).deriv
  have dBB := (((dd 0).const_mul (-2*k)).mul (de 0)).deriv
  change deriv B 0 = _ ∧ deriv (deriv B) 0 = _
  change deriv (fun t => -2*k*d t*e t) 0 = _ at dBB
  rw [dB,dBB]
  simp only [d,a,b,e,q,zero_smul,add_zero]
  constructor
  · trivial
  · ring

theorem planarRadialBarrier_partial (c z v : ℂ) (k r : ℝ) :
    planePartial v (planarRadialBarrier c k r) z =
      -2*k*((z.re-c.re)*v.re+(z.im-c.im)*v.im)*Real.exp (-k*dist z c^2) := by
  have h := parameter_line_hasDerivAt (f := planarRadialBarrier c k r) (v := v) (z := z) (t := 0)
    (by simpa using (planarRadialBarrier_analytic c z k r).differentiableAt)
  have eq := h.deriv.symm.trans (radial_line_derivatives c z v k r).1
  simpa only [zero_smul,add_zero,radialSquared_dist] using eq

theorem planarRadialBarrier_laplacian (c z : ℂ) (k r : ℝ) :
    (Δ (planarRadialBarrier c k r)) z = (4*k^2*dist z c^2-4*k)*Real.exp (-k*dist z c^2) := by
  have ha := planarRadialBarrier_analytic c z k r
  rw [laplacian_plane_partials ha,← analytic_plane_line_second_derivative ha 1,
    ← analytic_plane_line_second_derivative ha I,(radial_line_derivatives c z 1 k r).2,(radial_line_derivatives c z I k r).2,
    ← radialSquared_dist]
  simp only [Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add,one_pow,zero_pow (by decide : 2 ≠ 0)]
  dsimp [radialSquared]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planarRadialBarrier_laplacian
