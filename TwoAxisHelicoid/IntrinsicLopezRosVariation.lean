import TwoAxisHelicoid.IntrinsicHorizontalTorusFlux
import TwoAxisHelicoid.LopezRosFluxVariation

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- First-order closure here is imposed on the real periods of the actual
transformed coordinate forms, along each piecewise C¹ loop on the marked
surface, and does not posit finite-parameter closure. -/
def LopezRosClosedToFirstOrder (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) (k : ℝ → ℂ) : Prop :=
  ∀ {a b : ℂ} (γ : PiecewiseComplexPath (L.lattice : Set ℂ)ᶜ a b),
    periodTorusProjection L a = periodTorusProjection L b → ∀ j : Fin 2,
      HasDerivAt (fun s => (γ.integral (fun z => lopezRosHorizontal (k s)
        (torusImmersionForms L X z 0) (torusImmersionForms L X z 1) j)).re) 0 0

/-- On a harmonic conformal punctured torus with a nonvertical flux,
first-order closure of the López–Ros family precludes every nonzero real
amplitude velocity. The horizontal flux is measured on the quotient. -/
theorem intrinsic_lopez_ros_velocity_pure_imaginary (L : PeriodPair)
    (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hflux : HasIntrinsicNonverticalFlux L X) {k : ℝ → ℂ} {d : ℂ}
    (hk : HasDerivAt k d 0) (hk0 : k 0 = 1) (hclose : LopezRosClosedToFirstOrder L X k) : d.re = 0 := by
  obtain ⟨a,b,γ,hγ,hf⟩ := (nonvertical_flux_iff_intrinsic L X).mpr hflux
  obtain ⟨ha,_,hD⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  let p := torusImmersionForms L X
  have hp (j : Fin 3) : ContinuousOn (fun z => p z j) (L.lattice : Set ℂ)ᶜ :=
    fun z hz => (ha z hz j).continuousAt.continuousWithinAt
  have hperiod (j : Fin 3) : (γ.integral (fun z => p z j)).re = 0 := by
    have h := γ.integral_re_eq_sub (hp j) (X := fun z => torusFilledPosition L X (periodTorusProjection L z) j)
      (fun z hz => (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hD z hz))
    simpa [hγ] using h
  apply lopezRos_horizontal_real_velocity hk hk0 (hperiod 0) (hperiod 1) hf
  intro j
  have he := hclose γ hγ j
  change HasDerivAt (fun s => (γ.integral (fun z => lopezRosHorizontal (k s) (p z 0) (p z 1) j)).re) 0 0 at he
  simpa only [γ.integral_lopezRosHorizontal (hp 0) (hp 1)] using he

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.intrinsic_lopez_ros_velocity_pure_imaginary
