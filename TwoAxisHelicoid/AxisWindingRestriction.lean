import TwoAxisHelicoid.AxisTotalPhase
import TwoAxisHelicoid.SpinorSectionParity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered

namespace TwoAxisHelicoid
open Complex Set MeasureTheory

/-- The continuous relative phase on the whole closed vertical cycle,
normalized at its midpoint, for every integer in the Gauss family. -/
noncomputable def integerAxisPhase (t a : ℝ) (m : ℤ) (y : ℝ) : ℝ :=
  ∫ s in t..y, (axisClosedRegularOmega t a m (I*s)).re

theorem integerAxisPhase_continuous {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) : Continuous (integerAxisPhase t a m) := by
  have hc := Complex.continuous_re.comp (axisClosedRegularOmega_continuous ht ha m)
  exact continuous_iff_continuousAt.mpr (fun y =>
    (hc.integral_hasStrictDerivAt t y).hasDerivAt.continuousAt)

theorem integerAxisPhase_midpoint (t a : ℝ) (m : ℤ) : integerAxisPhase t a m t = 0 := by
  simp [integerAxisPhase]

theorem integerAxisPhase_total_increment {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) :
    integerAxisPhase t a m (2*t)-integerAxisPhase t a m 0 =
      2*Real.pi*(2*(m : ℝ)-1) := by
  have hc := Complex.continuous_re.comp (axisClosedRegularOmega_continuous ht ha m)
  change Continuous (fun y : ℝ => (axisClosedRegularOmega t a m (I*y)).re) at hc
  rw [integerAxisPhase,integerAxisPhase,intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable (μ := volume) t (2*t)) (hc.intervalIntegrable (μ := volume) t 0)]
  exact axisClosedRegularOmega_integral_re ht ha m

/-- An intermediate-value argument for a phase which cannot encounter the
two boundary angles in the open interval. Endpoint bounds are obtained by
continuity; no differentiability or monotonicity is required. -/
theorem continuous_phase_trapped {f : ℝ → ℝ} {L c A : ℝ}
    (hf : Continuous f) (hc : c ∈ Ioo (0 : ℝ) L) (hfc : f c = 0) (hA : 0 < A)
    (havoid : ∀ y ∈ Ioo (0 : ℝ) L, f y ≠ -A ∧ f y ≠ A) :
    MapsTo f (Icc 0 L) (Icc (-A) A) := by
  have hopen : MapsTo f (Ioo (0 : ℝ) L) (Ioo (-A) A) := by
    intro y hy
    constructor
    · by_contra hn
      have hle : f y ≤ -A := le_of_not_gt hn
      obtain ⟨z,hz,he⟩ := isPreconnected_Ioo.intermediate_value₂ hy hc hf.continuousOn
        (continuousOn_const : ContinuousOn (fun _ : ℝ => -A) (Ioo 0 L)) hle (by rw [hfc]; linarith)
      exact (havoid z hz).1 he
    · by_contra hn
      have hle : A ≤ f y := le_of_not_gt hn
      obtain ⟨z,hz,he⟩ := isPreconnected_Ioo.intermediate_value₂ hc hy hf.continuousOn
        (continuousOn_const : ContinuousOn (fun _ : ℝ => A) (Ioo 0 L)) (by rw [hfc]; exact hA.le) hle
      exact (havoid z hz).2 he
  have hsub : Ioo (0 : ℝ) L ⊆ f ⁻¹' Icc (-A) A := fun y hy =>
    ⟨(hopen hy).1.le,(hopen hy).2.le⟩
  have hclosed := closure_minimal hsub (isClosed_Icc.preimage hf)
  rwa [closure_Ioo (ne_of_lt (hc.1.trans hc.2))] at hclosed

/-- The analytic winding restriction. Applying this to an arbitrary surface
requires the separate geometric assertion that its relative tangent angle
avoids both boundary angles in the open vertical cycle. -/
theorem integerAxisPhase_parameter_zero_or_one {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ)
    (havoid : ∀ y ∈ Ioo (0 : ℝ) (2*t),
      integerAxisPhase t a m y ≠ -Real.pi ∧ integerAxisPhase t a m y ≠ Real.pi) :
    m = 0 ∨ m = 1 := by
  have hb := continuous_phase_trapped (integerAxisPhase_continuous ht ha m)
    (show t ∈ Ioo (0 : ℝ) (2*t) from ⟨ht,by linarith⟩)
    (integerAxisPhase_midpoint t a m) Real.pi_pos havoid
  have h0 := hb (show (0 : ℝ) ∈ Icc 0 (2*t) from ⟨le_rfl,by linarith⟩)
  have h2 := hb (show 2*t ∈ Icc (0 : ℝ) (2*t) from ⟨by linarith,le_rfl⟩)
  have he := integerAxisPhase_total_increment ht ha m
  have hπ : 0 < 4*Real.pi := by positivity
  have hmlo : 0 ≤ (m : ℝ) := (mul_nonneg_iff_of_pos_left hπ).mp (by nlinarith [h2.1,h0.2])
  have hmhi : (m : ℝ) ≤ 1 := (mul_le_mul_iff_right₀ hπ).mp (by nlinarith [h2.2,h0.1])
  have hi0 : (0 : ℤ) ≤ m := by exact_mod_cast hmlo
  have hi1 : m ≤ (1 : ℤ) := by exact_mod_cast hmhi
  omega

/-- Combines the proved analytic winding and flat-section dimension
computations. Both geometric inputs remain explicit hypotheses. -/
theorem integerAxisPhase_basic_parameter {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ)
    (havoid : ∀ y ∈ Ioo (0 : ℝ) (2*t),
      integerAxisPhase t a m y ≠ -Real.pi ∧ integerAxisPhase t a m y ≠ Real.pi)
    (hparity : Even (Module.finrank ℂ (flatHolomorphicSections t 1 ((-1 : ℂ)^m)))) : m = 1 :=
  integerSpinor_basic_parameter ht m (integerAxisPhase_parameter_zero_or_one ht ha m havoid) hparity

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.integerAxisPhase_total_increment
#print axioms TwoAxisHelicoid.integerAxisPhase_parameter_zero_or_one
#print axioms TwoAxisHelicoid.integerAxisPhase_basic_parameter
