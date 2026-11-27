import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Real Set
set_option maxHeartbeats 1000000

noncomputable def conformalKineticEnergy (φ : ℂ → ℝ) (z v : ℂ) : ℝ :=
  Real.exp (2*φ z)*Complex.normSq v

theorem complex_curve_normSq_hasDerivAt {v : ℝ → ℂ} {v' : ℂ} {t : ℝ}
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => Complex.normSq (v s))
      (2*((v t).re*v'.re+(v t).im*v'.im)) t := by
  have hr : HasDerivAt (fun s => (v s).re) v'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hv
  have hi : HasDerivAt (fun s => (v s).im) v'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hv
  convert (hr.pow 2).add (hi.pow 2) using 1
  · ext s
    change (v s).re*(v s).re+(v s).im*(v s).im = (v s).re^2+(v s).im^2
    ring
  · ring

/-- The conformal geodesic equation conserves the actual metric speed.
A common scalar cutoff in both state components preserves this identity. -/
theorem conformal_geodesic_energy_hasDerivAt_zero
    {φ : ℂ → ℝ} {Γ : ℂ → ℂ} {z v : ℝ → ℂ} {t χ : ℝ}
    (hφ : DifferentiableAt ℝ φ (z t))
    (hΓ : ∀ w : ℂ, fderiv ℝ φ (z t) w = (Γ (z t)*w).re)
    (hz : HasDerivAt z (χ • v t) t)
    (hv : HasDerivAt v (-(χ : ℂ)*Γ (z t)*(v t)^2) t) :
    HasDerivAt (fun s => conformalKineticEnergy φ (z s) (v s)) 0 t := by
  have hph := hφ.hasFDerivAt.comp_hasDerivAt t hz
  have heval : fderiv ℝ φ (z t) (χ • v t) = χ*(Γ (z t)*v t).re := by
    rw [map_smul,hΓ]
    rfl
  rw [heval] at hph
  have hnorm := complex_curve_normSq_hasDerivAt hv
  have he := ((hph.const_mul 2).exp).mul hnorm
  convert he using 1
  · rfl
  · simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
      Complex.ofReal_re,Complex.ofReal_im,pow_two,Function.comp_apply]
    ring

theorem conformal_geodesic_energy_constant
    {φ : ℂ → ℝ} {Γ : ℂ → ℂ} {z v : ℝ → ℂ} {χ : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ φ (z t))
    (hΓ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : ℂ, fderiv ℝ φ (z t) w = (Γ (z t)*w).re)
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt z (χ t • v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (-(χ t : ℂ)*Γ (z t)*(v t)^2) t) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      conformalKineticEnergy φ (z t) (v t) = conformalKineticEnergy φ (z 0) (v 0) := by
  have hd t ht := conformal_geodesic_energy_hasDerivAt_zero (hφ t ht) (hΓ t ht) (hz t ht) (hv t ht)
  intro t ht
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) t ht
  simp only [zero_mul,norm_le_zero_iff,sub_eq_zero] at he
  exact he

theorem conformal_unit_energy_velocity_bound {φ : ℂ → ℝ} {z v : ℂ}
    (hφ : 0 ≤ φ z) (hE : conformalKineticEnergy φ z v = 1) : ‖v‖ ≤ 1 := by
  have hexp : 1 ≤ Real.exp (2*φ z) := Real.one_le_exp_iff.mpr (by positivity)
  have hnorm := Complex.normSq_nonneg v
  have hs : ‖v‖^2 = Complex.normSq v := Complex.sq_norm v
  dsimp [conformalKineticEnergy] at hE
  nlinarith [norm_nonneg v,mul_nonneg (sub_nonneg.mpr hexp) hnorm]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conformal_geodesic_energy_constant
