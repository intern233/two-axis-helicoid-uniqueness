import TwoAxisHelicoid.SpinorQuadraticSurjectivity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Complex Real Set Metric
set_option maxHeartbeats 1000000

abbrev UnitSpinor := {s : ℂ × ℂ // spinorWeight s = 1}
abbrev UnitNullFrame := {p : Fin 3 → ℂ // ComplexNull p ∧ nullMetric p = 1}

theorem spinorWeight_neg (s : ℂ × ℂ) : spinorWeight (-s) = spinorWeight s := by
  simp [spinorWeight]

theorem unitSpinor_ne_zero (s : UnitSpinor) : s.1 ≠ 0 := by
  intro he
  have hh := s.2
  rw [he] at hh
  norm_num [spinorWeight] at hh

theorem unitSpinor_set_isCompact : IsCompact {s : ℂ × ℂ | spinorWeight s = 1} := by
  apply (isCompact_closedBall (0 : ℂ × ℂ) 1).of_isClosed_subset
  · exact isClosed_eq spinorWeight_continuous continuous_const
  · intro s hs
    rw [mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff]
    have hw : normSq s.1+normSq s.2 = 1 := hs
    constructor
    · apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
      rw [← normSq_eq_norm_sq]
      norm_num only [one_pow]
      linarith [normSq_nonneg s.2]
    · apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
      rw [← normSq_eq_norm_sq]
      norm_num only [one_pow]
      linarith [normSq_nonneg s.1]

instance unitSpinor_compactSpace : CompactSpace UnitSpinor :=
  isCompact_iff_compactSpace.mp unitSpinor_set_isCompact

noncomputable def unitSpinorQuadratic : UnitSpinor → UnitNullFrame := fun s =>
  ⟨spinorQuadratic s.1,spinorQuadratic_null s.1,by rw [spinorQuadratic_metric,s.2]; norm_num⟩

theorem unitSpinorQuadratic_continuous : Continuous unitSpinorQuadratic :=
  (spinorQuadratic_continuous.comp continuous_subtype_val).subtype_mk _

theorem unitSpinorQuadratic_surjective : Function.Surjective unitSpinorQuadratic := by
  intro p
  obtain ⟨s,hs,hsp⟩ := spinorQuadratic_surjective_unit_null p.2.1 p.2.2
  exact ⟨⟨s,hs⟩,Subtype.ext hsp⟩

noncomputable def unitSpinorAntipode : UnitSpinor ≃ₜ UnitSpinor where
  toFun s := ⟨-s.1,by rw [spinorWeight_neg,s.2]⟩
  invFun s := ⟨-s.1,by rw [spinorWeight_neg,s.2]⟩
  left_inv s := Subtype.ext (neg_neg s.1)
  right_inv s := Subtype.ext (neg_neg s.1)
  continuous_toFun := continuous_subtype_val.neg.subtype_mk (fun s => by
    change spinorWeight (-s.1) = 1
    rw [spinorWeight_neg,s.2])
  continuous_invFun := continuous_subtype_val.neg.subtype_mk (fun s => by
    change spinorWeight (-s.1) = 1
    rw [spinorWeight_neg,s.2])

theorem unitSpinorAntipode_involutive (s : UnitSpinor) :
    unitSpinorAntipode (unitSpinorAntipode s) = s := Subtype.ext (neg_neg s.1)

theorem unitSpinorAntipode_ne (s : UnitSpinor) : unitSpinorAntipode s ≠ s := by
  intro he
  have hv := congrArg Subtype.val he
  have h1 := congrArg (fun p : ℂ × ℂ => p.1) hv
  have h2 := congrArg (fun p : ℂ × ℂ => p.2) hv
  apply unitSpinor_ne_zero s
  apply Prod.ext
  · change -s.1.1 = s.1.1 at h1
    change s.1.1 = 0
    linear_combination -h1/2
  · change -s.1.2 = s.1.2 at h2
    change s.1.2 = 0
    linear_combination -h2/2

theorem unitSpinorAntipode_isometry : Isometry unitSpinorAntipode := by
  apply Isometry.of_dist_eq
  intro s t
  change dist (-s.1) (-t.1) = dist s.1 t.1
  exact dist_neg_neg _ _

theorem unitSpinorQuadratic_fibers {s t : UnitSpinor} :
    unitSpinorQuadratic s = unitSpinorQuadratic t ↔ s = t ∨ s = unitSpinorAntipode t := by
  rw [Subtype.ext_iff]
  change spinorQuadratic s.1 = spinorQuadratic t.1 ↔ _
  rw [spinorQuadratic_eq_iff]
  constructor
  · rintro (he | he)
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext he)
  · rintro (he | he)
    · exact Or.inl (congrArg Subtype.val he)
    · exact Or.inr (congrArg Subtype.val he)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unitSpinorQuadratic_surjective
#print axioms TwoAxisHelicoid.unitSpinorQuadratic_fibers
