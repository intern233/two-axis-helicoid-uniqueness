import TwoAxisHelicoid.AnalyticFinitePeriodParameters
import TwoAxisHelicoid.CompactCoreFiniteSimilarityClasses

namespace TwoAxisHelicoid
open Set

/-- Every pitch-normalized single-valued explicit immersion, including
nonembedded ones, is represented by one of finitely many spatial classes,
using the analytic endpoint argument alone. -/
theorem analytic_pitch_class_finiteness :
    (range (fun W : PitchNormalizedBasicImmersion => Quotient.mk (spatialSimilaritySetoid _) W.image)).Finite := by
  classical
  let rep (t : ℝ) : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))) :=
    if h : ∃ W : PitchNormalizedBasicImmersion, W.t = t then Quotient.mk _ h.choose.image else Quotient.mk _ ∅
  apply (actualPeriodAlong_finite_zero_parameters_analytic.image rep).subset
  rintro _ ⟨W,rfl⟩
  have he : ∃ Y : PitchNormalizedBasicImmersion, Y.t = W.t := ⟨W,rfl⟩
  have hc : W.c ≠ 0 := by
    intro hc
    have h := W.scale
    rw [hc,abs_zero] at h
    linarith [(verticalA_spec ⟨W.ht,W.hT⟩).1.2]
  have hH := (periodic_actual_primitive_period_equations W.ht (verticalA_spec ⟨W.ht,W.hT⟩).1 hc W.differential W.periodic).2
  refine ⟨W.t,⟨⟨W.ht,W.hT⟩,hH⟩,?_⟩
  simp only [rep,dite_eq_left he]
  exact Quotient.sound (pitch_normalized_images_similar_of_equal_height he.choose W he.choose_spec)

theorem analytic_pitch_height_gap (W : PitchNormalizedBasicImmersion) : 1/8 < W.t := by
  have ha := (verticalA_spec ⟨W.ht,W.hT⟩).1
  have hc : W.c ≠ 0 := by intro hc; have e := W.scale; rw [hc,abs_zero] at e; linarith [ha.2]
  exact actualPeriodAlong_zero_height_gt_eighth W.ht
    (periodic_actual_primitive_period_equations W.ht ha hc W.differential W.periodic).2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_pitch_class_finiteness
