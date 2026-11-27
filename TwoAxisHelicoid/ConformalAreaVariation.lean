import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace TwoAxisHelicoid
open Real Filter
open scoped Topology

noncomputable def areaQuartic (g A B C s : ℝ) : ℝ := g^2+A*s^2+B*s^3+C*s^4
noncomputable def areaQuarticD (A B C s : ℝ) : ℝ := 2*A*s+3*B*s^2+4*C*s^3

theorem areaQuartic_hasDerivAt (g A B C s : ℝ) :
    HasDerivAt (areaQuartic g A B C) (areaQuarticD A B C s) s := by
  have h := HasDerivAt.add (HasDerivAt.add
    ((((hasDerivAt_id s).pow 2).const_mul A).const_add (g^2))
    (((hasDerivAt_id s).pow 3).const_mul B)) (((hasDerivAt_id s).pow 4).const_mul C)
  convert h using 1
  · rfl
  · simp [areaQuarticD]
    ring

theorem areaQuarticD_hasDerivAt_zero (A B C : ℝ) :
    HasDerivAt (areaQuarticD A B C) (2*A) 0 := by
  have h := HasDerivAt.add (HasDerivAt.add ((hasDerivAt_id (0 : ℝ)).const_mul (2*A))
    (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (3*B)))
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul (4*C))
  convert h using 1
  · rfl
  · norm_num

theorem areaQuartic_sqrt_second_derivative {g : ℝ} (hg : 0 < g) (A B C : ℝ) :
    HasDerivAt (deriv (fun s => Real.sqrt (areaQuartic g A B C s))) (A/g) 0 := by
  have hq0 : areaQuartic g A B C 0 = g^2 := by simp [areaQuartic]
  have hd0 : areaQuarticD A B C 0 = 0 := by simp [areaQuarticD]
  have hqpos : 0 < areaQuartic g A B C 0 := by rw [hq0]; positivity
  have hsq := (areaQuartic_hasDerivAt g A B C 0).sqrt hqpos.ne'
  have hden : 2*Real.sqrt (areaQuartic g A B C 0) ≠ 0 := by positivity
  have hquot := (areaQuarticD_hasDerivAt_zero A B C).div (hsq.const_mul 2) hden
  have he : deriv (fun s => Real.sqrt (areaQuartic g A B C s)) =ᶠ[𝓝 0]
      (fun s => areaQuarticD A B C s/(2*Real.sqrt (areaQuartic g A B C s))) := by
    filter_upwards [(areaQuartic_hasDerivAt g A B C 0).continuousAt.eventually
      (Ioi_mem_nhds hqpos)] with s hs
    exact ((areaQuartic_hasDerivAt g A B C s).sqrt (ne_of_gt hs)).deriv
  apply (HasDerivAt.congr_of_eventuallyEq ?_ he)
  convert hquot using 1
  rw [hq0,hd0,Real.sqrt_sq hg.le]
  field_simp [hg.ne']
  ring

/-- Gram determinant of a normal variation of a conformal minimal
immersion. Here g is the first fundamental coefficient, b,c are the two
independent second fundamental coefficients, and u,ux,uy are the test
function's value and derivatives. -/
noncomputable def normalVariationArea (g b c u ux uy s : ℝ) : ℝ :=
  Real.sqrt ((g-2*s*u*b+s^2*(u^2*(b^2+c^2)/g+ux^2))*
      (g+2*s*u*b+s^2*(u^2*(b^2+c^2)/g+uy^2))-
    (-2*s*u*c+s^2*ux*uy)^2)

theorem normalVariationArea_eq_quartic {g : ℝ} (hg : g ≠ 0)
    (b c u ux uy : ℝ) :
    normalVariationArea g b c u ux uy = fun s => Real.sqrt
      (areaQuartic g (g*(ux^2+uy^2)-2*u^2*(b^2+c^2))
        (2*u*b*(ux^2-uy^2)+4*u*c*ux*uy)
        (u^4*(b^2+c^2)^2/g^2+u^2*(b^2+c^2)/g*(ux^2+uy^2)) s) := by
  funext s
  unfold normalVariationArea areaQuartic
  congr 1
  field_simp [hg]
  ring

/-- Exact pointwise second variation of the conformal area density. This
calculus result does not assume the second-variation formula. -/
theorem conformal_normal_area_second_variation {g : ℝ} (hg : 0 < g)
    (b c u ux uy : ℝ) :
    HasDerivAt (deriv (normalVariationArea g b c u ux uy))
      (ux^2+uy^2-(2*(b^2+c^2)/g)*u^2) 0 := by
  rw [normalVariationArea_eq_quartic hg.ne']
  convert areaQuartic_sqrt_second_derivative hg
    (g*(ux^2+uy^2)-2*u^2*(b^2+c^2))
    (2*u*b*(ux^2-uy^2)+4*u*c*ux*uy)
    (u^4*(b^2+c^2)^2/g^2+u^2*(b^2+c^2)/g*(ux^2+uy^2)) using 1
  field_simp [hg.ne']

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conformal_normal_area_second_variation
