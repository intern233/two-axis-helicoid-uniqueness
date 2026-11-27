import TwoAxisHelicoid.CompactNegativeDirection
import Mathlib.MeasureTheory.Integral.Prod

namespace TwoAxisHelicoid
open Set MeasureTheory Function
open scoped ContDiff
set_option maxHeartbeats 1000000

noncomputable def lineMass (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, f x^2
noncomputable def lineDirichletEnergy (f : ℝ → ℝ) : ℝ := ∫ x : ℝ, (deriv f x)^2
noncomputable def lineSchrodingerEnergy (V f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, (deriv f x)^2-V x*f x^2
noncomputable def planarSchrodingerEnergy (V : ℝ → ℝ) (v : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, (deriv (fun x => v (x,p.2)) p.1)^2+
    (deriv (fun y => v (p.1,y)) p.2)^2-V p.2*v p^2

theorem smooth_compact_square_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : Integrable (fun x => f x^2) := by
  have hc : Continuous (fun x => f x^2) := hf.continuous.pow 2
  exact hc.integrable_of_hasCompactSupport
    (hs.comp_left (g := fun y : ℝ => y^2) (by norm_num))

theorem smooth_compact_deriv_square_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : Integrable (fun x => (deriv f x)^2) := by
  have hc : Continuous (fun x => (deriv f x)^2) := (hf.continuous_deriv (by simp)).pow 2
  exact hc.integrable_of_hasCompactSupport
    (hs.deriv.comp_left (g := fun y : ℝ => y^2) (by norm_num))

theorem smooth_compact_line_energy_integrable {V f : ℝ → ℝ} (hV : Continuous V)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Integrable (fun x => (deriv f x)^2-V x*f x^2) :=
  (smooth_compact_deriv_square_integrable hf hs).sub
    ((hV.mul (hf.continuous.pow 2)).integrable_of_hasCompactSupport
      (show HasCompactSupport (fun x => V x*f x^2) from
        (hs.comp_left (g := fun y : ℝ => y^2) (by norm_num)).mul_left))

theorem smooth_compact_tensor {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.1*g p.2) ∧
      HasCompactSupport (fun p : ℝ × ℝ => f p.1*g p.2) := by
  refine ⟨(hf.comp contDiff_fst).mul (hg.comp contDiff_snd),?_⟩
  apply HasCompactSupport.of_support_subset_isCompact (hsf.isCompact.prod hsg.isCompact)
  intro p hp
  have hnon : f p.1*g p.2 ≠ 0 := hp
  exact ⟨subset_closure ((mul_ne_zero_iff.mp hnon).1),
    subset_closure ((mul_ne_zero_iff.mp hnon).2)⟩

theorem planarSchrodingerEnergy_tensor {V f g : ℝ → ℝ} (hV : Continuous V)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    planarSchrodingerEnergy V (fun p => f p.1*g p.2) =
      lineDirichletEnergy f*lineMass g+lineMass f*lineSchrodingerEnergy V g := by
  have hdx (x y : ℝ) : deriv (fun w => f w*g y) x = deriv f x*g y :=
    (((hf.differentiable (by simp)) x).hasDerivAt.mul_const (g y)).deriv
  have hdy (x y : ℝ) : deriv (fun w => f x*g w) y = f x*deriv g y :=
    (((hg.differentiable (by simp)) y).hasDerivAt.const_mul (f x)).deriv
  have h1 := (smooth_compact_deriv_square_integrable hf hsf).mul_prod
    (smooth_compact_square_integrable hg hsg)
  have h2 := (smooth_compact_square_integrable hf hsf).mul_prod
    (smooth_compact_line_energy_integrable hV hg hsg)
  unfold planarSchrodingerEnergy
  simp_rw [hdx,hdy]
  calc
    _ = ∫ p : ℝ × ℝ, ((deriv f p.1)^2*g p.2^2+
        f p.1^2*((deriv g p.2)^2-V p.2*g p.2^2)) := by
      congr 1
      funext p
      ring
    _ = _ := by
      rw [Measure.volume_eq_prod,integral_add h1 h2,
        integral_prod_mul (fun x : ℝ => (deriv f x)^2) (fun y : ℝ => g y^2),
        integral_prod_mul (fun x : ℝ => f x^2) (fun y : ℝ => (deriv g y)^2-V y*g y^2)]
      rfl

theorem smooth_compact_dilate {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun x => f (x/R)) ∧ HasCompactSupport (fun x => f (x/R)) := by
  refine ⟨hf.comp (contDiff_id.div_const R),?_⟩
  simpa only [smul_eq_mul,mul_comm,← div_eq_mul_inv] using hs.comp_smul (inv_ne_zero hR.ne')

theorem lineMass_dilate (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    lineMass (fun x => f (x/R)) = R*lineMass f := by
  unfold lineMass
  rw [Measure.integral_comp_div (fun x : ℝ => f x^2) R]
  simp only [abs_of_pos hR,smul_eq_mul]

theorem lineDirichletEnergy_dilate {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {R : ℝ} (hR : 0 < R) :
    lineDirichletEnergy (fun x => f (x/R)) = lineDirichletEnergy f/R := by
  have hd (x : ℝ) : deriv (fun y => f (y/R)) x = deriv f (x/R)/R := by
    simpa only [Function.comp_def,id_eq,one_div,one_mul,div_eq_mul_inv] using
      ((hf (x/R)).hasDerivAt.comp x ((hasDerivAt_id x).div_const R)).deriv
  unfold lineDirichletEnergy
  simp_rw [hd,div_pow]
  rw [integral_div,Measure.integral_comp_div (fun x : ℝ => (deriv f x)^2) R]
  simp only [abs_of_pos hR,smul_eq_mul]
  field_simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.planarSchrodingerEnergy_tensor
#print axioms TwoAxisHelicoid.lineDirichletEnergy_dilate
