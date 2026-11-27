import TwoAxisHelicoid.HarmonicTorusGaussRigidity
import TwoAxisHelicoid.TorusIntegralCoherentLift

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Horizontal flux detected along an actual closed path of the quotient
with the integral of the immersion's own coordinate differential. -/
def HasIntrinsicNonverticalFlux (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) : Prop :=
  ∃ (q : PuncturedPeriodTorus L) (γ : Path q q) (j : Fin 3) (v : ℂ), j ≠ 2 ∧
    TorusPathIntegral L (fun z => torusImmersionForms L X z j) γ v ∧ v.im ≠ 0

theorem nonvertical_flux_iff_intrinsic (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) :
    HasNonverticalTorusFlux L X ↔ HasIntrinsicNonverticalFlux L X := by
  constructor
  · rintro ⟨x,y,p,hxy,he⟩
    obtain ⟨j,hj,hv⟩ : ∃ j : Fin 3, j ≠ 2 ∧ (p.integral (fun z => torusImmersionForms L X z j)).im ≠ 0 :=
      he.elim (fun h => ⟨0,by decide,h⟩) (fun h => ⟨1,by decide,h⟩)
    obtain ⟨_,_,γ,hγ⟩ := p.projected_hasIntegral (fun z => torusImmersionForms L X z j)
    exact ⟨_,_,j,_,hj,hγ.cast rfl (Subtype.ext hxy),hv⟩
  · rintro ⟨q,γ,j,v,hj,hv,hn⟩
    obtain ⟨x,hx⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) q.1
    obtain ⟨y,hy,p,he⟩ := hv.coherent_lift
      (fun z ω hω => congrFun (torusImmersionForms_periodic L X z ω hω) j) x hx
    change p.integral (fun z => torusImmersionForms L X z j) = v at he
    have h : (p.integral (fun z => torusImmersionForms L X z j)).im ≠ 0 := by rwa [he]
    refine ⟨x,y,p,hx.trans hy.symm,?_⟩
    fin_cases j
    · exact .inl h
    · exact .inr h
    · exact False.elim (hj rfl)

theorem intrinsic_punctured_torus_fixed_log_rigidity (L : PeriodPair)
    (X Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z)
    (ho : meromorphicOrderAt (fun z => torusImmersionForms L X z 2) 0 = (-2:ℤ))
    (hh : ∀ z ∉ L.lattice, torusImmersionForms L Y z 2 = torusImmersionForms L X z 2)
    (hlog : ∀ z ∉ L.lattice, torusImmersionForms L X z 2 ≠ 0 →
      immersionGaussLog (torusImmersionForms L Y) z = immersionGaussLog (torusImmersionForms L X) z)
    (hflux : HasIntrinsicNonverticalFlux L X) :
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, ∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+d :=
  harmonic_punctured_torus_fixed_log_rigidity L X Y hX hY ho hh hlog ((nonvertical_flux_iff_intrinsic L X).mpr hflux)

/-- The Laurent-principal-part comparison with a geometric flux hypothesis
on actual quotient loops, independent of all charts used to express the
principal parts. -/
theorem intrinsic_punctured_torus_fixed_parts_rigidity (L : PeriodPair)
    (X Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z)
    (ho : meromorphicOrderAt (fun z => torusImmersionForms L X z 2) 0 = (-2:ℤ))
    (hH : CommonLaurentPartAt (fun z => torusImmersionForms L X z 2) (fun z => torusImmersionForms L Y z 2) 0)
    (hΩ : ∀ z, CommonLaurentPartAt (immersionGaussLog (torusImmersionForms L X))
      (immersionGaussLog (torusImmersionForms L Y)) z)
    (hflux : HasIntrinsicNonverticalFlux L X) :
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, ∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+d :=
  harmonic_punctured_torus_fixed_laurent_rigidity L X Y hX hY ho hH hΩ ((nonvertical_flux_iff_intrinsic L X).mpr hflux)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.intrinsic_punctured_torus_fixed_parts_rigidity
