import TwoAxisHelicoid.RootPeriodPartialDerivative
import TwoAxisHelicoid.RootRectanglePeriodContinuity

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA thetaJet thetaQuotient

theorem root_midline_integral_continuous (F : ℝ → ℝ → ℂ → ℂ)
    (hf : Continuous (fun p : (RootHeight × RootAbscissa) × ℝ =>
      F p.1.1 p.1.2 ((p.2 : ℂ)+I*((p.1.1/2 : ℝ) : ℂ)))) :
    Continuous (fun p : RootHeight × RootAbscissa =>
      (∫ x : ℝ in (-1)..0, F p.1 p.2 ((x : ℂ)+I*((p.1/2 : ℝ) : ℂ))).re) := by
  let : CompactSpace RootHeight := isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace RootAbscissa := isCompact_iff_compactSpace.mp isCompact_Icc
  have hi := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (p : RootHeight × RootAbscissa) (x : ℝ) => F p.1 p.2
      ((x : ℂ)+I*((p.1/2 : ℝ) : ℂ))) hf (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))
  have hi' : Continuous (fun p : RootHeight × RootAbscissa =>
      ∫ x : ℝ in (-1)..0, F p.1 p.2 ((x : ℂ)+I*((p.1/2 : ℝ) : ℂ))) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      integral_Icc_eq_integral_Ioc] using hi
  exact Complex.continuous_re.comp hi'

theorem root_period_partials_continuous :
    Continuous (fun p : RootHeight × RootAbscissa => rootPeriodDa p.1 p.2) ∧
    Continuous (fun p : RootHeight × RootAbscissa => rootPeriodDt p.1 p.2) := by
  have hc := root_composite_continuousOn (S := (Set.univ : Set ((RootHeight × RootAbscissa) × ℝ)))
    (u := fun p => (p.1.1 : ℝ)) (b := fun p => (p.1.2 : ℝ)) (x := Prod.snd)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun p _ => p.1.1.property) (fun p _ => p.1.2.property)
  exact ⟨root_midline_integral_continuous thetaAa (continuousOn_univ.mp hc.2.1),
    root_midline_integral_continuous thetaAtMidline (continuousOn_univ.mp hc.2.2)⟩

theorem root_period_partials_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => rootPeriodDa p.1 p.2) rootRectangle ∧
    ContinuousOn (fun p : ℝ × ℝ => rootPeriodDt p.1 p.2) rootRectangle := by
  let m : rootRectangle → RootHeight × RootAbscissa := fun p =>
    (⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩)
  have hm : Continuous m := by dsimp [m]; fun_prop
  constructor
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact root_period_partials_continuous.1.comp hm
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact root_period_partials_continuous.2.comp hm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_period_partials_continuousOn
