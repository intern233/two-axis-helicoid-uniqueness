import TwoAxisHelicoid.EllipticPrincipalPart
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000

theorem period_pair_real_linear_coefficient_zero (L : PeriodPair) {c : ℂ}
    (h₁ : (c*L.ω₁).re=0) (h₂ : (c*L.ω₂).re=0) : c=0 := by
  have hz (z : ℂ) : (c*z).re=0 := by
    have he : (L.basis.repr z 0) • L.ω₁+(L.basis.repr z 1) • L.ω₂=z := by
      simpa only [Fin.sum_univ_two,L.basis_zero,L.basis_one] using L.basis.sum_repr z
    rw [← he]
    simp only [Complex.real_smul,Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h₁ h₂ ⊢
    linear_combination (L.basis.repr z 0)*h₁+(L.basis.repr z 1)*h₂
  by_contra hc
  have h := hz c⁻¹
  rw [mul_inv_cancel₀ hc] at h
  norm_num at h

noncomputable def ellipticLinePeriod (f : ℂ → ℂ) (z ω : ℂ) : ℂ :=
  ∫ s : ℝ in (0)..1, ω*f (z+(s : ℂ)*ω)

theorem ellipticLinePeriod_integrable (L : PeriodPair) {f : ℂ → ℂ} {z ω : ℂ}
    (hf : ∀ w ∉ L.lattice, DifferentiableAt ℂ f w)
    (hreg : ∀ s ∈ Icc (0 : ℝ) 1, z+(s : ℂ)*ω ∉ L.lattice) :
    IntervalIntegrable (fun s : ℝ => ω*f (z+(s : ℂ)*ω)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  intro s hs
  exact (continuousAt_const.mul ((hf _ (hreg s hs)).continuousAt.comp
    (f := fun u : ℝ => z+(u : ℂ)*ω)
    (by fun_prop : ContinuousAt (fun u : ℝ => z+(u : ℂ)*ω) s))).continuousWithinAt

theorem ellipticLinePeriod_difference_constant (L : PeriodPair) {f g : ℂ → ℂ} {c z ω : ℂ}
    (hf : ∀ w ∉ L.lattice, DifferentiableAt ℂ f w)
    (hg : ∀ w ∉ L.lattice, DifferentiableAt ℂ g w)
    (hreg : ∀ s ∈ Icc (0 : ℝ) 1, z+(s : ℂ)*ω ∉ L.lattice)
    (he : ∀ w ∉ L.lattice, f w-g w=c) :
    ellipticLinePeriod f z ω-ellipticLinePeriod g z ω=ω*c := by
  unfold ellipticLinePeriod
  rw [← intervalIntegral.integral_sub (ellipticLinePeriod_integrable L hf hreg)
    (ellipticLinePeriod_integrable L hg hreg)]
  calc
    _ = ∫ s : ℝ in (0)..1, ω*c := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hr := hreg s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs)
      change ω*f (z+(s : ℂ)*ω)-ω*g (z+(s : ℂ)*ω)=ω*c
      rw [← mul_sub,he _ hr]
    _ = _ := by simp

/-- Real-period normalization for a differential on an arbitrary marked
complex torus with one double pole: equal explicit principal parts and equal
real periods on the two genuine generator paths force equal coefficients.
The paths avoid the pole lattice, and all periods here are actual integrals. -/
theorem elliptic_same_double_principal_part_real_period_unique (L : PeriodPair)
    {f₁ f₂ g₁ g₂ : ℂ → ℂ} (A z₁ z₂ : ℂ)
    (hf₁ : ∀ z ∉ L.lattice, DifferentiableAt ℂ f₁ z)
    (hf₂ : ∀ z ∉ L.lattice, DifferentiableAt ℂ f₂ z)
    (hp₁ : ∀ z ω, ω ∈ L.lattice → f₁ (z+ω)=f₁ z)
    (hp₂ : ∀ z ω, ω ∈ L.lattice → f₂ (z+ω)=f₂ z)
    (hg₁ : AnalyticAt ℂ g₁ 0) (hg₂ : AnalyticAt ℂ g₂ 0)
    (hl₁ : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f₁ z=A/z^2+g₁ z)
    (hl₂ : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f₂ z=A/z^2+g₂ z)
    (hr₁ : ∀ s ∈ Icc (0 : ℝ) 1, z₁+(s : ℂ)*L.ω₁ ∉ L.lattice)
    (hr₂ : ∀ s ∈ Icc (0 : ℝ) 1, z₂+(s : ℂ)*L.ω₂ ∉ L.lattice)
    (hP₁ : (ellipticLinePeriod f₁ z₁ L.ω₁).re=(ellipticLinePeriod f₂ z₁ L.ω₁).re)
    (hP₂ : (ellipticLinePeriod f₁ z₂ L.ω₂).re=(ellipticLinePeriod f₂ z₂ L.ω₂).re) :
    ∀ z ∉ L.lattice, f₁ z=f₂ z := by
  have h₁ := elliptic_double_pole_classification L A hf₁ hp₁ hg₁ hl₁
  have h₂ := elliptic_double_pole_classification L A hf₂ hp₂ hg₂ hl₂
  have hc (z : ℂ) (hz : z ∉ L.lattice) : f₁ z-f₂ z=g₁ 0-g₂ 0 := by rw [h₁ z hz,h₂ z hz]; ring
  have hI₁ := ellipticLinePeriod_difference_constant L hf₁ hf₂ hr₁ hc
  have hI₂ := ellipticLinePeriod_difference_constant L hf₁ hf₂ hr₂ hc
  have hzero : g₁ 0-g₂ 0=0 := by
    apply period_pair_real_linear_coefficient_zero L
    · have h := congrArg Complex.re hI₁
      rw [Complex.sub_re,hP₁,sub_self,mul_comm] at h
      exact h.symm
    · have h := congrArg Complex.re hI₂
      rw [Complex.sub_re,hP₂,sub_self,mul_comm] at h
      exact h.symm
  intro z hz
  exact sub_eq_zero.mp ((hc z hz).trans hzero)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.elliptic_same_double_principal_part_real_period_unique
