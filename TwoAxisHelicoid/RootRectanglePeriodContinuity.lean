import TwoAxisHelicoid.RootCompositeContinuity
import TwoAxisHelicoid.RootVerticalContinuity

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA thetaJet thetaQuotient

theorem root_rectangle_period_continuous :
    Continuous (fun p : RootHeight × RootAbscissa => thetaHorizontalPeriod p.1 p.2) := by
  let : CompactSpace RootHeight := isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace RootAbscissa := isCompact_iff_compactSpace.mp isCompact_Icc
  have hc := root_composite_continuousOn (S := (Set.univ : Set ((RootHeight × RootAbscissa) × ℝ)))
    (u := fun p => (p.1.1 : ℝ)) (b := fun p => (p.1.2 : ℝ)) (x := Prod.snd)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun p _ => p.1.1.property) (fun p _ => p.1.2.property)
  have hf : Continuous (fun p : (RootHeight × RootAbscissa) × ℝ =>
      thetaA p.1.1 p.1.2 ((p.2 : ℂ)+I*((p.1.1/2 : ℝ) : ℂ))) :=
    continuousOn_univ.mp hc.1
  have hi := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (p : RootHeight × RootAbscissa) (x : ℝ) => thetaA p.1 p.2
      ((x : ℂ)+I*((p.1/2 : ℝ) : ℂ))) hf (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))
  have heq (p : RootHeight × RootAbscissa) : thetaHorizontalPeriod p.1 p.2 =
      (∫ x in Icc (-1 : ℝ) 0, thetaA p.1 p.2 ((x : ℂ)+I*((p.1/2 : ℝ) : ℂ))).re := by
    rw [root_horizontal_period_half p.1.property.1 p.1.property.2 p.2,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0), integral_Icc_eq_integral_Ioc]
  convert Complex.continuous_re.comp hi using 1
  funext p
  exact heq p

theorem root_period_fixed_t_continuousOn {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) :
    ContinuousOn (thetaHorizontalPeriod t) (Icc (rootALower : ℝ) rootAUpper) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact root_rectangle_period_continuous.comp
    (show Continuous (fun a : RootAbscissa => ((⟨t,htl,htu⟩ : RootHeight),a)) by fun_prop)

theorem root_period_fixed_a_continuousOn {a : ℝ}
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    ContinuousOn (fun t => thetaHorizontalPeriod t a) (Icc (rootTLower : ℝ) rootTUpper) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact root_rectangle_period_continuous.comp
    (show Continuous (fun t : RootHeight => (t,(⟨a,hal,hau⟩ : RootAbscissa))) by fun_prop)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_rectangle_period_continuous
