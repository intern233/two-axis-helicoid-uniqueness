import TwoAxisHelicoid.NonperiodicCompactnessCutoffs
import TwoAxisHelicoid.AxisHelicoidGauge
import TwoAxisHelicoid.LeastPeriodCutoff

namespace TwoAxisHelicoid
open Complex Set

/-- The half-period convention of Hoffman–White, §7, p. 807. -/
def positiveScrewHalfPeriods (S : Set (Fin 3 → ℝ)) : Set ℝ :=
  {r | 0<r ∧ unitHelicoidScrew r '' S=S}

theorem measured_screw_cutoff_iff {S : Set (Fin 3 → ℝ)} {h : WithTop ℝ}
    (record : LeastPeriodOrInfinity (positiveScrewHalfPeriods S) h) (η : ℝ) :
    (η : WithTop ℝ)≤h ↔ HasNoScrewBelow η S := by
  rw [least_period_cutoff_iff record]
  exact ⟨fun no r pos short period => no r ⟨pos,period⟩ short,
    fun cut r hr short => cut r hr.1 short hr.2⟩

/-- A half-period parameter translates the real height by twice that parameter. -/
theorem unit_screw_moves_reference_ruling (h b u v : ℝ) : unitHelicoidScrew h (axisRuledHelicoid I 1 b ⟨u,v⟩)=
      axisRuledHelicoid I 1 b ⟨u,v+2*h⟩ := by
  change verticalRotation (exp ((2*h:ℝ)*I)) (axisRuledHelicoid I 1 b ⟨u,v⟩)+![0,0,2*h]=_
  have angle : v+2*h-b=(v-b)+2*h := by ring
  simp only [axisRuledHelicoid_ruling,verticalRotation_apply,exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im,one_mul,angle,Real.cos_add,Real.sin_add]
  ext j
  fin_cases j <;> simp <;> ring

/-- Every screw step of the positive unit-pitch reference helicoid preserves
its entire image, for any choice of the reference height of its ruling. -/
theorem unit_screw_preserves_reference_helicoid (h b : ℝ) :
    unitHelicoidScrew h '' range (axisRuledHelicoid I 1 b)=range (axisRuledHelicoid I 1 b) := by
  apply Subset.antisymm
  · rintro _ ⟨_,⟨⟨u,v⟩,rfl⟩,rfl⟩
    exact ⟨⟨u,v+2*h⟩,(unit_screw_moves_reference_ruling h b u v).symm⟩
  · rintro _ ⟨⟨u,v⟩,rfl⟩
    refine ⟨_,mem_range_self ⟨u,v-2*h⟩,?_⟩
    simpa only [sub_add_cancel] using unit_screw_moves_reference_ruling h b u (v-2*h)

/-- Membership in a fixed positive period cutoff rules out the standard
helicoid as limiting image before any topological handle argument. -/
theorem positive_cutoff_excludes_reference_helicoid {η : ℝ} (hp : 0<η) {S : Set (Fin 3 → ℝ)}
    (cut : HasNoScrewBelow η S) (b : ℝ) : S≠range (axisRuledHelicoid I 1 b) := by
  rintro rfl
  exact cut (η/2) (half_pos hp) (half_lt_self hp) (unit_screw_preserves_reference_helicoid _ _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unit_screw_moves_reference_ruling
#print axioms TwoAxisHelicoid.measured_screw_cutoff_iff
#print axioms TwoAxisHelicoid.unit_screw_preserves_reference_helicoid
#print axioms TwoAxisHelicoid.positive_cutoff_excludes_reference_helicoid
