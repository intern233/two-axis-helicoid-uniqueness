import TwoAxisHelicoid.PlaneWeakClassicalFlux
import TwoAxisHelicoid.PlaneWeakConductivity
import TwoAxisHelicoid.PlaneHarmonicCoordinateConjugate
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

private theorem mixed_partials {φ : ℂ → ℝ} (s : ContDiff ℝ ∞ φ) (z v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) z w = fderiv ℝ (fun y => fderiv ℝ φ y w) z v := by
  have ss : ContDiff ℝ ∞ (fderiv ℝ φ) := s.fderiv_right (by simp)
  have e (d : ℂ) : fderiv ℝ (fun y => fderiv ℝ φ y d) z =
      ((ContinuousLinearMap.apply ℝ ℝ d).comp (fderiv ℝ (fderiv ℝ φ) z)) :=
    ((ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp z
      (ss.differentiable (by simp) z).hasFDerivAt).fderiv
  rw [e v, e w]
  exact s.contDiffAt.isSymmSndFDerivAt (by simp) w v

private theorem rotated_test_gradients_orthogonal {φ ψ : ℂ → ℝ}
    (sφ : ContDiff ℝ ∞ φ) (sψ : ContDiff ℝ ∞ ψ) (hφ : HasCompactSupport φ) :
    (∫ z, fderiv ℝ ψ z 1 * fderiv ℝ φ z I - fderiv ℝ ψ z I * fderiv ℝ φ z 1) = 0 := by
  let a := fun z => fderiv ℝ ψ z 1
  let b := fun z => fderiv ℝ ψ z I
  have sa : ContDiff ℝ ∞ a := (sψ.fderiv_right (by simp)).clm_apply contDiff_const
  have sb : ContDiff ℝ ∞ b := (sψ.fderiv_right (by simp)).clm_apply contDiff_const
  have int (v : ℂ) (c : ℂ → ℝ) (sc : Continuous c) : Integrable (fun z => c z * fderiv ℝ φ z v) := by
    apply (sc.mul ((sφ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
    exact (hφ.fderiv_apply ℝ v).mul_left
  rw [integral_sub (int I a sa.continuous) (int 1 b sb.continuous),
    plane_smooth_test_integration_by_parts sa sφ hφ I, plane_smooth_test_integration_by_parts sb sφ hφ 1]
  have eq : (fun z => fderiv ℝ a z I)=(fun z => fderiv ℝ b z 1) := funext fun z => mixed_partials sψ z 1 I
  simp_rw [show ∀ z, fderiv ℝ a z I=fderiv ℝ b z 1 from congrFun eq]
  exact sub_self _

/-- Every smooth representative of an energy limit of scalar test gradients
is the gradient of an actual globally smooth scalar potential on the plane. -/
theorem smooth_representative_gradient_has_potential (u : Lp ℂ 2 (volume : Measure ℂ))
    (hu : u ∈ planeDirichletGradients volume univ) {f : ℂ → ℂ}
    (rep : ⇑u =ᵐ[volume] f) (sf : ContDiff ℝ ∞ f) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ ∀ z, planeTestGradient g z=f z := by
  have sr : ContDiff ℝ ∞ (fun z => (f z).re) := reCLM.contDiff.comp sf
  have si : ContDiff ℝ ∞ (fun z => (f z).im) := imCLM.contDiff.comp sf
  have curl := smooth_plane_flux_divergence_zero isOpen_univ si sr.neg
  have closed (z : ℂ) : fderiv ℝ (fun y => (f y).im) z 1=fderiv ℝ (fun y => (f y).re) z I := by
    have all := curl (fun ψ s h _ => by
      let grad := (planeTestGradient_memLp (μ:=volume) s h).toLp (planeTestGradient ψ)
      let rot : Lp ℂ 2 (volume : Measure ℂ) := I • grad
      have rotated : ⇑rot =ᵐ[volume] (fun y => I * planeTestGradient ψ y) := by
        filter_upwards [Lp.coeFn_smul I grad,(planeTestGradient_memLp (μ:=volume) s h).coeFn_toLp] with y a b
        change (I • grad) y=_
        rw [a,Pi.smul_apply,b,smul_eq_mul]
      let L := innerSL ℝ rot
      have incl : planeDirichletGradients volume univ ≤ L.ker := by
        apply Submodule.topologicalClosure_minimal _ _ L.isClosed_ker
        apply Submodule.span_le.mpr
        rintro w ⟨φ,sφ,hφ,_,hw⟩
        change inner ℝ rot w=0
        rw [L2.inner_def]
        refine (integral_congr_ae ?_).trans (rotated_test_gradients_orthogonal sφ s hφ)
        filter_upwards [rotated,hw] with y a b
        change inner ℝ (rot y) (w y)=_
        rw [a,b]
        simp only [planeTestGradient,Complex.inner,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.conj_re,Complex.conj_im]
        ring
      have orth : inner ℝ rot u=0 := incl hu
      rw [L2.inner_def] at orth
      refine (integral_congr_ae ?_).trans orth
      filter_upwards [rotated,rep] with y a b
      change (f y).im * fderiv ℝ ψ y 1 + (-(f y).re) * fderiv ℝ ψ y I = inner ℝ (rot y) (u y)
      rw [a,b]
      simp only [planeTestGradient,Complex.inner,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.conj_re,Complex.conj_im]
      ring) z (mem_univ z)
    change fderiv ℝ (fun y => (f y).im) z 1+fderiv ℝ (fun y => -(f y).re) z I=0 at all
    rw [fderiv_fun_neg,neg_apply] at all
    linarith
  obtain ⟨g,hg⟩ := smooth_plane_primitive isOpen_univ convex_univ (fun z _ => sr.contDiffAt)
    (fun z _ => si.contDiffAt) (fun z _ => closed z)
  refine ⟨g,contDiff_iff_contDiffAt.mpr (fun z => (hg z (mem_univ z)).1),?_⟩
  intro z
  have e := (hg z (mem_univ z)).2.fderiv
  apply Complex.ext <;> simp [planeTestGradient,e]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_representative_gradient_has_potential
