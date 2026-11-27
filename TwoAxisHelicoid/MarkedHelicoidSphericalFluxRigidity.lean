import TwoAxisHelicoid.MarkedEmbeddedHelicoidFluxRigidity
import TwoAxisHelicoid.HelicoidGraphHeightNonconstant
import TwoAxisHelicoid.TorusSphericalGaussRigidity

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- The two rigidity assertions of Appendix C on a genuinely embedded
marked helicoid. The entire spherical Gauss map rotates, including both
poles. The nonconstant-height input is derived from the graph end. -/
theorem embedded_marked_helicoid_spherical_rigidity (bbs : MarkedBernsteinBreinerFluxPrinciple)
    (L : PeriodPair) (X Y : PuncturedPeriodTorus L → Fin 3 → ℝ) (hX : MarkedEmbeddedHelicoidForFlux L X)
    (hY : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z) :
    ((∀ z ∉ L.lattice, torusImmersionForms L Y z 2 = torusImmersionForms L X z 2) →
      (∀ z ∉ L.lattice, torusImmersionForms L X z 2 ≠ 0 →
        immersionGaussLog (torusImmersionForms L Y) z = immersionGaussLog (torusImmersionForms L X) z) →
      ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, (∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+d) ∧
        ∀ q, torusSphericalGauss L Y q = OnePoint.map (exp ((θ:ℂ)*I)*·) (torusSphericalGauss L X q)) ∧
    (CommonLaurentPartAt (fun z => torusImmersionForms L X z 2) (fun z => torusImmersionForms L Y z 2) 0 →
      (∀ z, CommonLaurentPartAt (immersionGaussLog (torusImmersionForms L X)) (immersionGaussLog (torusImmersionForms L Y)) z) →
      ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, ∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+d) := by
  obtain ⟨x,y,γ,hclose,hγ⟩ := (nonvertical_flux_iff_intrinsic L X).mpr
    ((torus_spatial_nonvertical_flux_iff L X hX.regular).mp (bbs L X hX))
  obtain ⟨k,u,b,_,_,hend⟩ := hX.asymptotic
  obtain ⟨z,hz,hn⟩ := marked_helicoid_graph_height_form_nonzero L X hX.regular hend
  obtain ⟨hp,hpn,hpD⟩ := torusImmersionForms_regular L X (fun z hz => (hX.regular z hz).1) (fun z hz => (hX.regular z hz).2)
  obtain ⟨hq,hqn,hqD⟩ := torusImmersionForms_regular L Y (fun z hz => (hY z hz).1) (fun z hz => (hY z hz).2)
  constructor
  · intro hh hl
    obtain ⟨θ,d,he⟩ := punctured_torus_fixed_gauss_log_rigid_motion L _ _ _ _ hp hq hpn hqn hpD hqD hh hl hz hn γ hclose hγ
    have E (q : PuncturedPeriodTorus L) : Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+d := by
      simpa only [torusFilledPosition_eq] using he q
    exact ⟨θ,d,E,torusSphericalGauss_rotate L X Y hX.regular hY (by simp [Complex.norm_exp]) E⟩
  · intro hh hl
    obtain ⟨θ,d,he⟩ := marked_torus_common_laurent_parts_rigid_motion L _ _ _ _ hp hq hpn hqn
      (torusImmersionForms_periodic L X) (torusImmersionForms_periodic L Y) hpD hqD hh hl hz hn γ hclose hγ
    exact ⟨θ,d,fun q => by simpa only [torusFilledPosition_eq] using he q⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_marked_helicoid_spherical_rigidity
