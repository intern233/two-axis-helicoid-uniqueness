import TwoAxisHelicoid.LogGaussSphere
import TwoAxisHelicoid.HelicoidEndPotential
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

namespace TwoAxisHelicoid
open Complex Real

noncomputable def holomorphicLogGaussNormal (W : ℂ → ℂ) (z : ℂ) : Fin 3 → ℝ :=
  logGaussSphere (W z).re (W z).im

theorem holomorphicLogGaussNormal_line_hasDerivAt {W : ℂ → ℂ} {D z : ℂ}
    (hW : HasDerivAt W D z) (w : ℂ) :
    HasDerivAt (fun s : ℝ => holomorphicLogGaussNormal W (z+(s : ℂ)*w))
      ((w*D).re • logGaussSphereU (W z).re (W z).im+
        (w*D).im • logGaussSphereV (W z).re (W z).im) 0 := by
  have hi : HasDerivAt (fun s : ℝ => z+(s : ℂ)*w) w 0 := by
    have h := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_id (0 : ℝ))).mul_const w).const_add z
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul,Function.comp_def,id_eq] using h
  have hW' : HasDerivAt W D (z+((0 : ℝ) : ℂ)*w) := by simpa using hW
  have hw : HasDerivAt (fun s : ℝ => W (z+(s : ℂ)*w)) (w*D) 0 := by
    exact (hW'.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hi
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hw
  have hm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hw
  simpa only [holomorphicLogGaussNormal,Function.comp_def,Complex.reCLM_apply,
    Complex.imCLM_apply,Complex.ofReal_zero,zero_mul,add_zero] using
    logGaussSphere_curve_hasDerivAt hr hm

theorem holomorphicLogGaussNormal_energy {W : ℂ → ℂ} {D z : ℂ}
    (hW : HasDerivAt W D z) :
    ∃ nx ny : Fin 3 → ℝ,
      HasDerivAt (fun s : ℝ => holomorphicLogGaussNormal W (z+(s : ℂ))) nx 0 ∧
      HasDerivAt (fun s : ℝ => holomorphicLogGaussNormal W (z+I*(s : ℂ))) ny 0 ∧
      (∑ j, ((nx j)^2+(ny j)^2)) = 2*‖D‖^2/(Real.cosh (W z).re)^2 := by
  let u := (W z).re
  let v := (W z).im
  let nx := D.re • logGaussSphereU u v+D.im • logGaussSphereV u v
  let ny := -D.im • logGaussSphereU u v+D.re • logGaussSphereV u v
  refine ⟨nx,ny,?_,?_,?_⟩
  · simpa only [mul_one,one_mul] using holomorphicLogGaussNormal_line_hasDerivAt hW 1
  · simpa [ny,u,v,Complex.mul_re,Complex.mul_im,mul_comm (I : ℂ)] using
      holomorphicLogGaussNormal_line_hasDerivAt hW I
  · change (∑ j, ((D.re*logGaussSphereU u v j+D.im*logGaussSphereV u v j)^2+
        (-D.im*logGaussSphereU u v j+D.re*logGaussSphereV u v j)^2)) = _
    rw [Finset.sum_add_distrib]
    rw [logGaussSphere_combination_energy,logGaussSphere_combination_energy]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply]
    dsimp [u]
    ring

/-- The manuscript end potential is exactly the Euclidean Dirichlet energy
density of the actual Gauss-sphere normal determined by its holomorphic
logarithm. No potential limit is assumed here. -/
theorem helicoidEndPotential_eq_gauss_normal_energy {F : ℂ → ℂ} {α : ℝ}
    {p : ℝ × ℝ} (hF : DifferentiableAt ℂ F (planeComplex p)) :
    let W : ℂ → ℂ := fun z => (I*(α : ℂ))*z+F z
    ∃ nx ny : Fin 3 → ℝ,
      HasDerivAt (fun s : ℝ => holomorphicLogGaussNormal W (planeComplex p+(s : ℂ))) nx 0 ∧
      HasDerivAt (fun s : ℝ => holomorphicLogGaussNormal W (planeComplex p+I*(s : ℂ))) ny 0 ∧
      (∑ j, ((nx j)^2+(ny j)^2)) = helicoidEndPotential α F (deriv F) p := by
  dsimp only
  have hW := ((hasDerivAt_id (planeComplex p)).const_mul (I*(α : ℂ))).add hF.hasDerivAt
  simp only [mul_one,id_eq] at hW
  obtain ⟨nx,ny,hx,hy,he⟩ := holomorphicLogGaussNormal_energy hW
  refine ⟨nx,ny,hx,hy,?_⟩
  rw [he]
  unfold helicoidEndPotential endPotentialKernel helicoidGroundState
  simp only [Pi.add_apply,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add,
    zero_sub,planeComplex_im]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidEndPotential_eq_gauss_normal_energy
