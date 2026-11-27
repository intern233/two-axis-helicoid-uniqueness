import TwoAxisHelicoid.IntrinsicHorizontalTorusFlux
import TwoAxisHelicoid.GaussFromVerticalRotation

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology

/-- The phase is shared by the actual Gauss data and the global immersions. -/
theorem intrinsic_gauss_and_immersion_phase_rigidity (L : PeriodPair)
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
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ,
      (∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (X q)+d) ∧
      ∀ z ∉ L.lattice, nullGauss (torusImmersionForms L Y z) =
        exp ((θ:ℂ)*I)*nullGauss (torusImmersionForms L X z) := by
  obtain ⟨θ,d,he⟩ := intrinsic_punctured_torus_fixed_log_rigidity L X Y hX hY ho hh hlog hflux
  refine ⟨θ,d,he,?_⟩
  intro z hz
  let c := exp ((θ:ℂ)*I)
  have hc : ‖c‖ = 1 := by simp [c,Complex.norm_exp]
  apply nullGauss_of_rotated_real_derivative hc
  have hD (Z : PuncturedPeriodTorus L → Fin 3 → ℝ)
      (hZ : ∀ u ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Z w j) u) ∧
        ConformalCoordinateDerivatives (puncturedTorusPullback L Z) u) :=
    (torusImmersionForms_regular L Z (fun u hu => (hZ u hu).1) (fun u hu => (hZ u hu).2)).2.2 z hz
  have hnear : (torusFilledPosition L Y ∘ periodTorusProjection L) =ᶠ[𝓝 z]
      (fun u => verticalRotation c ((torusFilledPosition L X ∘ periodTorusProjection L) u)+d) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with u hu
    let q : PuncturedPeriodTorus L := ⟨periodTorusProjection L u,
      fun h => hu ((periodTorusProjection_eq_zero L u).mp h)⟩
    change torusFilledPosition L Y q.1 = verticalRotation c (torusFilledPosition L X q.1)+d
    simpa only [torusFilledPosition_eq] using he q
  exact (hD Y hY).unique ((((verticalRotation c).hasFDerivAt.comp z (hD X hX)).add_const d).congr_of_eventuallyEq hnear)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.intrinsic_gauss_and_immersion_phase_rigidity
