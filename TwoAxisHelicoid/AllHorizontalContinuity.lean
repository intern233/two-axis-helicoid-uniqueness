import TwoAxisHelicoid.AllHorizontalRegularity
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA thetaJet thetaQuotient

def horizontalDomain : Set (ℝ × ℝ) := Ioi (0:ℝ) ×ˢ Ioo (0:ℝ) 2

theorem horizontalDomain_isOpen : IsOpen horizontalDomain := isOpen_Ioi.prod isOpen_Ioo

theorem intervalIntegral_parameter_continuousOn {S : Set (ℝ × ℝ)} (ho : IsOpen S)
    {f : (ℝ × ℝ) → ℝ → ℂ}
    (hc : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => f p.1 p.2) (S ×ˢ univ)) (l u : ℝ) (hlu : l ≤ u) :
    ContinuousOn (fun p => ∫ x in l..u, f p x) S := by
  let : LocallyCompactSpace S := ho.locallyCompactSpace
  have hm : Continuous (fun p : S × ℝ => ((p.1 : ℝ × ℝ),p.2)) := by fun_prop
  have hf : Continuous (fun p : S × ℝ => f p.1 p.2) :=
    hc.comp_continuous hm (fun p => ⟨p.1.property,mem_univ _⟩)
  have hi := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (p : S) (x : ℝ) => f p x) hf (isCompact_Icc : IsCompact (Icc l u))
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun p : S => ∫ x in l..u, f (p:ℝ × ℝ) x)
  simpa only [intervalIntegral.integral_of_le hlu,integral_Icc_eq_integral_Ioc] using hi

noncomputable def horizontalPeriodDa (t a : ℝ) : ℝ :=
  (∫ x : ℝ in (-1)..0, thetaAa t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re

noncomputable def horizontalPeriodDt (t a : ℝ) : ℝ :=
  (∫ x : ℝ in (-1)..0, thetaAtMidline t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re

theorem horizontal_period_and_partials_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => thetaHorizontalPeriod p.1 p.2) horizontalDomain ∧
    ContinuousOn (fun p : ℝ × ℝ => horizontalPeriodDa p.1 p.2) horizontalDomain ∧
    ContinuousOn (fun p : ℝ × ℝ => horizontalPeriodDt p.1 p.2) horizontalDomain := by
  have hc := horizontal_composite_continuousOn (S := horizontalDomain ×ˢ (univ : Set ℝ))
    (u := fun p : (ℝ × ℝ) × ℝ => p.1.1) (b := fun p => p.1.2) (x := Prod.snd)
    (by fun_prop) (by fun_prop) (by fun_prop) (fun _ hp => hp.1.1) (fun _ hp => hp.1.2)
  have hA := Complex.continuous_re.comp_continuousOn
    (intervalIntegral_parameter_continuousOn horizontalDomain_isOpen
      (f := fun p x => thetaA p.1 p.2 ((x:ℂ)+I*((p.1/2:ℝ):ℂ))) hc.1 (-1) 0 (by norm_num))
  have hDa := Complex.continuous_re.comp_continuousOn
    (intervalIntegral_parameter_continuousOn horizontalDomain_isOpen
      (f := fun p x => thetaAa p.1 p.2 ((x:ℂ)+I*((p.1/2:ℝ):ℂ))) hc.2.1 (-1) 0 (by norm_num))
  have hDt := Complex.continuous_re.comp_continuousOn
    (intervalIntegral_parameter_continuousOn horizontalDomain_isOpen
      (f := fun p x => thetaAtMidline p.1 p.2 ((x:ℂ)+I*((p.1/2:ℝ):ℂ))) hc.2.2 (-1) 0 (by norm_num))
  refine ⟨?_,hDa,hDt⟩
  apply hA.congr
  intro p hp
  exact horizontal_period_half hp.1 p.2

theorem horizontal_period_joint_continuousAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    ContinuousAt (fun p : ℝ × ℝ => thetaHorizontalPeriod p.1 p.2) (t,a) :=
  horizontal_period_and_partials_continuousOn.1.continuousAt
    (horizontalDomain_isOpen.mem_nhds ⟨ht,ha⟩)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_period_joint_continuousAt
