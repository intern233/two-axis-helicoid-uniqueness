import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace TwoAxisHelicoid
open Complex Real Set Filter MeasureTheory Metric
open scoped Interval Topology

theorem complex_polar_eq_circle (r θ : ℝ) : Complex.polarCoord.symm (r,θ)=circleMap 0 r θ := by
  rw [Complex.polarCoord_symm_apply,circleMap_zero,Complex.exp_mul_I]
  simp

/-- Polar integration on a finite annulus needs regularity only on
that closed annulus. Both angular endpoints and the two radial
circles have the conventions of the usual interval integral. -/
theorem complex_annulus_integral_polar {J : ℂ → ℝ} {r R : ℝ} (hr : 0<r) (lt : r<R)
    (cJ : ContinuousOn J {z | r≤‖z‖ ∧ ‖z‖≤R}) :
    (∫ z in {z : ℂ | r<‖z‖ ∧ ‖z‖<R}, J z)=
      ∫ s in r..R, ∫ θ in (-π)..π, s*J (circleMap 0 s θ) := by
  let S : Set ℂ := {z | r<‖z‖ ∧ ‖z‖<R}
  let C := Ioo r R ×ˢ Ioo (-π) π
  let T := Ioi (0:ℝ) ×ˢ Ioo (-π) π
  let f := fun p : ℝ × ℝ => p.1*J (Complex.polarCoord.symm p)
  have ms : MeasurableSet S := ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet
  have mc : MeasurableSet C := measurableSet_Ioo.prod measurableSet_Ioo
  have mt : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have sub : C⊆T := fun _ hp => ⟨hr.trans hp.1.1,hp.2⟩
  have pc : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have c : ContinuousOn f (Icc r R ×ˢ Icc (-π) π) :=
    continuous_fst.continuousOn.mul (cJ.comp pc.continuousOn (by
      intro p hp
      change r≤‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖≤R
      rw [Complex.norm_polarCoord_symm,abs_of_nonneg (hr.le.trans hp.1.1)]
      exact hp.1))
  have ci := c.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) (μ := (volume : Measure (ℝ × ℝ)))
  have ic : IntegrableOn f C ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ci.mono_set (fun _ hp => ⟨Ioo_subset_Icc_self hp.1,Ioo_subset_Icc_self hp.2⟩)
  have eq : (fun p : ℝ × ℝ => p.1 • S.indicator J (Complex.polarCoord.symm p))
      =ᵐ[volume.restrict T] C.indicator f := by
    apply (ae_restrict_iff' mt).mpr (ae_of_all _ ?_)
    intro p hp
    have n := Complex.norm_polarCoord_symm p
    rw [abs_of_pos hp.1] at n
    change p.1 • S.indicator J (Complex.polarCoord.symm p)=C.indicator f p
    by_cases h : p.1∈Ioo r R
    · have src : Complex.polarCoord.symm p∈S := by change r<_ ∧ _<R; rw [n]; exact h
      rw [indicator_of_mem src,indicator_of_mem (show p∈C from ⟨h,hp.2⟩)]
      rfl
    · have src : Complex.polarCoord.symm p∉S := by intro b; apply h; change r<p.1 ∧ p.1<R; simpa only [S,mem_ofPred_eq,n] using b
      rw [indicator_of_notMem src,smul_zero,indicator_of_notMem (show p∉C from fun b => h b.1)]
  have hpi : -π≤π := by linarith [Real.pi_pos]
  calc
    (∫ z in S, J z) = ∫ p in T, p.1 • S.indicator J (Complex.polarCoord.symm p) := by
      rw [← integral_indicator ms,← Complex.integral_comp_polarCoord_symm]
      rfl
    _ = ∫ p in C, f p := by
      rw [integral_congr_ae eq,setIntegral_indicator mc]
      rw [inter_eq_right.mpr sub]
    _ = ∫ s in Ioo r R, ∫ θ in Ioo (-π) π, f (s,θ) := by
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod f ic
    _ = ∫ s in r..R, ∫ θ in (-π)..π, s*J (circleMap 0 s θ) := by
      simp only [intervalIntegral.integral_of_le lt.le,intervalIntegral.integral_of_le hpi,
        Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ))),f,complex_polar_eq_circle]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_annulus_integral_polar
