import TwoAxisHelicoid.HarmonicTorusRigidityData
import TwoAxisHelicoid.TorusPrincipalPartFluxRigidity

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- A geometric horizontal flux witness. Its components are the imaginary
periods of the coordinate differentials obtained from the real derivative
of the original map, along a closed piecewise C¹ loop of the quotient. -/
def HasNonverticalTorusFlux (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) : Prop :=
  ∃ (x y : ℂ) (γ : PiecewiseComplexPath (L.lattice : Set ℂ)ᶜ x y),
    periodTorusProjection L x = periodTorusProjection L y ∧
    ((γ.integral (fun z => torusImmersionForms L X z 0)).im ≠ 0 ∨
      (γ.integral (fun z => torusImmersionForms L X z 1)).im ≠ 0)

/-- Fixed-height/logarithmic rigidity for actual harmonic conformal maps on
the punctured quotient. All its Weierstrass coefficients are obtained from
the position maps, and the comparison is asserted on the full surface. -/
theorem harmonic_punctured_torus_fixed_log_rigidity (L : PeriodPair)
    (X Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z)
    (ho : meromorphicOrderAt (fun z => torusImmersionForms L X z 2) 0 = (-2:ℤ))
    (hh : ∀ z ∉ L.lattice, torusImmersionForms L Y z 2 = torusImmersionForms L X z 2)
    (hlog : ∀ z ∉ L.lattice, torusImmersionForms L X z 2 ≠ 0 →
      immersionGaussLog (torusImmersionForms L Y) z = immersionGaussLog (torusImmersionForms L X) z)
    (hflux : HasNonverticalTorusFlux L X) :
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, ∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+d := by
  obtain ⟨x,y,γ,hclose,hγ⟩ := hflux
  obtain ⟨b,hb,hbn⟩ := height_differential_nonzero_at_regular_point L ho
  obtain ⟨hp,hpn,hpD⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  obtain ⟨hq,hqn,hqD⟩ := torusImmersionForms_regular L Y (fun z hz => (hY z hz).1) (fun z hz => (hY z hz).2)
  obtain ⟨θ,d,he⟩ := punctured_torus_fixed_gauss_log_rigid_motion L _ _ _ _ hp hq hpn hqn hpD hqD
    hh hlog hb hbn γ hclose hγ
  exact ⟨θ,d,fun q => by simpa only [torusFilledPosition_eq] using he q⟩

/-- Fixed Laurent parts for the height at the single end and for the Gauss
logarithmic differential at all points give a spatial rotation and
translation; no divisor data or coordinate differential are supplied
independently of the actual immersions. -/
theorem harmonic_punctured_torus_fixed_laurent_rigidity (L : PeriodPair)
    (X Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z)
    (ho : meromorphicOrderAt (fun z => torusImmersionForms L X z 2) 0 = (-2:ℤ))
    (hH : CommonLaurentPartAt (fun z => torusImmersionForms L X z 2) (fun z => torusImmersionForms L Y z 2) 0)
    (hΩ : ∀ z, CommonLaurentPartAt (immersionGaussLog (torusImmersionForms L X))
      (immersionGaussLog (torusImmersionForms L Y)) z)
    (hflux : HasNonverticalTorusFlux L X) :
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, ∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+d := by
  obtain ⟨x,y,γ,hclose,hγ⟩ := hflux
  obtain ⟨b,hb,hbn⟩ := height_differential_nonzero_at_regular_point L ho
  obtain ⟨hp,hpn,hpD⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  obtain ⟨hq,hqn,hqD⟩ := torusImmersionForms_regular L Y (fun z hz => (hY z hz).1) (fun z hz => (hY z hz).2)
  obtain ⟨θ,d,he⟩ := marked_torus_common_laurent_parts_rigid_motion L _ _ _ _ hp hq hpn hqn
    (torusImmersionForms_periodic L X) (torusImmersionForms_periodic L Y) hpD hqD hH hΩ hb hbn γ hclose hγ
  exact ⟨θ,d,fun q => by simpa only [torusFilledPosition_eq] using he q⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_punctured_torus_fixed_log_rigidity
#print axioms TwoAxisHelicoid.harmonic_punctured_torus_fixed_laurent_rigidity
