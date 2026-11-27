import TwoAxisHelicoid.RhombicAxisRelativeDirection
import Mathlib.Analysis.Normed.Module.Normalize

namespace TwoAxisHelicoid
open Complex Set Filter Topology NormedSpace
open scoped Topology

/-- The direction seen from inside the marked parameter strip. At
its right edge the inward derivative has the opposite sign. -/
noncomputable def rhombicStripDirection (n : ℤ) (P : ℂ → ℂ) (w : ℂ) : ℂ :=
  if w.re=n then NormedSpace.normalize (fderiv ℝ P w 1) else
    if w.re=(n:ℝ)+1 then -NormedSpace.normalize (fderiv ℝ P w 1) else NormedSpace.normalize (P w)

def closedParameterStrip (n : ℤ) : Set ℂ := {w | w.re ∈ Icc (n:ℝ) (n+1)}

private theorem normalized_continuousAt {f : ℂ → ℂ} {z : ℂ} (cf : ContinuousAt f z) (nz : f z≠0) :
    ContinuousAt (fun w => NormedSpace.normalize (f w)) z :=
  (cf.norm.inv₀ (norm_ne_zero_iff.mpr nz)).smul cf

/-- The rotating direction of the actual surface extends continuously
over both finite vertical edges. Every regular value is unit length,
and multiplying by the true horizontal radius recovers the position
in the rotating frame. -/
theorem rhombic_closed_strip_unit_direction {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hi : Function.Injective (harmonicTorusImmersion hX)) (α b : ℝ) (n : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) (inside : z ∈ closedParameterStrip n) :
    let P := fun w => helicoidRelativeHorizontal α b (X w)
    let D := rhombicStripDirection n P
    ContinuousWithinAt D (closedParameterStrip n) z ∧ ‖D z‖=1 ∧ P z=(‖P z‖:ℂ)*D z := by
  let P := fun w => helicoidRelativeHorizontal α b (X w)
  let D := rhombicStripDirection n P
  let S := closedParameterStrip n
  change ContinuousWithinAt D S z ∧ ‖D z‖=1 ∧ P z=(‖P z‖:ℂ)*D z
  have leftlt : (n:ℝ)<n+1 := by linarith
  have reps {c : ℤ} (h : z.re=c) := rhombic_axis_relative_direction ht hX hi α b hz h
  have zero_of_axis {c : ℤ} (h : z.re=c) : P z=0 := (reps h).2.1
  by_cases left : z.re=n
  · let Q := verticalTransverseDifference P n
    have atz := reps left
    have good : ∀ᶠ w in 𝓝[S] z, D w=NormedSpace.normalize (Q w) := by
      have small : ∀ᶠ w in 𝓝 z, w.re<(n:ℝ)+1 := continuous_re.continuousAt.eventually_lt continuousAt_const (by rw [left]; exact leftlt)
      filter_upwards [self_mem_nhdsWithin,small.filter_mono nhdsWithin_le_nhds,
        atz.2.2.2.2.2.filter_mono nhdsWithin_le_nhds] with w hw hh form
      by_cases same : w.re=n
      · simp [D,rhombicStripDirection,same,Q,verticalTransverseDifference_on P same]
      · have positive : 0<w.re-n := sub_pos.mpr (lt_of_le_of_ne hw.1 (Ne.symm same))
        have fact : P w=(w.re-n) • Q w := form
        simp only [D,rhombicStripDirection,ite_eq_right same,ite_eq_right hh.ne,fact,normalize_smul_of_pos positive]
    have atD : D z=NormedSpace.normalize (Q z) := by simp [D,rhombicStripDirection,left,Q,verticalTransverseDifference_on P left]
    refine ⟨((normalized_continuousAt atz.2.2.2.2.1 atz.2.2.2.1).continuousWithinAt).congr_of_eventuallyEq good atD,
      atD.symm ▸ norm_normalize atz.2.2.2.1,?_⟩
    simp [zero_of_axis left]
  by_cases right : z.re=(n:ℝ)+1
  · have cast : ((n+1:ℤ):ℝ)=(n:ℝ)+1 := by push_cast; rfl
    have hn : z.re=((n+1:ℤ):ℝ) := right.trans cast.symm
    let Q := verticalTransverseDifference P (n+1 : ℤ)
    have atz := reps hn
    have good : ∀ᶠ w in 𝓝[S] z, D w= -NormedSpace.normalize (Q w) := by
      have big : ∀ᶠ w in 𝓝 z, (n:ℝ)<w.re := continuousAt_const.eventually_lt continuous_re.continuousAt (by rw [right]; exact leftlt)
      filter_upwards [self_mem_nhdsWithin,big.filter_mono nhdsWithin_le_nhds,
        atz.2.2.2.2.2.filter_mono nhdsWithin_le_nhds] with w hw hh form
      by_cases same : w.re=(n:ℝ)+1
      · have eq := same.trans cast.symm
        simp only [D,rhombicStripDirection,ite_eq_right hh.ne',ite_eq_left same,Q,verticalTransverseDifference_on P eq]
      · have neg : w.re-((n+1:ℤ):ℝ)<0 := sub_neg.mpr (cast ▸ lt_of_le_of_ne hw.2 same)
        have fact : P w=(w.re-((n+1:ℤ):ℝ)) • Q w := form
        simp only [D,rhombicStripDirection,ite_eq_right hh.ne',ite_eq_right same,fact,normalize_smul_of_neg neg]
    have atD : D z= -NormedSpace.normalize (Q z) := by simp only [D,rhombicStripDirection,ite_eq_right left,ite_eq_left right,Q,verticalTransverseDifference_on P hn]
    refine ⟨(normalized_continuousAt atz.2.2.2.2.1 atz.2.2.2.1).neg.continuousWithinAt.congr_of_eventuallyEq good atD,
      ?_,?_⟩
    · rw [atD,norm_neg]; exact norm_normalize atz.2.2.2.1
    · simp [zero_of_axis hn]
  have nz : P z≠0 := by
    intro eq
    have bv := (helicoidRelativeHorizontal_eq_zero_iff α b _).mp eq
    obtain ⟨k,hk⟩ := (rhombic_physical_axes_preimages ht hX hi hz).1.mp bv
    have l : (n:ℝ)<(k:ℝ) := hk ▸ lt_of_le_of_ne inside.1 (Ne.symm left)
    have r : (k:ℝ)<(n+1:ℤ) := by
      push_cast
      exact hk ▸ lt_of_le_of_ne inside.2 right
    have l' : n<k := by exact_mod_cast l
    have r' : k<n+1 := by exact_mod_cast r
    omega
  have ax : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hX.harmonic z hz j)
  have cp : ContinuousAt P z := ((helicoidRelativeHorizontal_analytic α b _).comp ax).continuousAt
  have eq : D =ᶠ[𝓝 z] fun w => NormedSpace.normalize (P w) := by
    filter_upwards [continuous_re.continuousAt.eventually_ne left,continuous_re.continuousAt.eventually_ne right] with w a c
    simp [D,rhombicStripDirection,a,c]
  refine ⟨((normalized_continuousAt cp nz).congr_of_eventuallyEq eq).continuousWithinAt,eq.self_of_nhds.symm ▸ norm_normalize nz,?_⟩
  rw [eq.self_of_nhds]
  exact (norm_smul_normalize (P z)).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_closed_strip_unit_direction
