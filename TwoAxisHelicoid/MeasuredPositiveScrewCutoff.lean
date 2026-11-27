import TwoAxisHelicoid.ScrewMotionGroupLaw
import TwoAxisHelicoid.StandardHelicoidPeriodCutoff
import TwoAxisHelicoid.PositiveDifferencePeriodMinimum

namespace TwoAxisHelicoid
open Complex Set Topology

open Classical in
/-- Read the period from the actual set of spatial screw symmetries. -/
noncomputable def physicalScrewHalfPeriod (S : Set (Fin 3 → ℝ)) : WithTop ℝ :=
  if (positiveScrewHalfPeriods S).Nonempty then (sInf (positiveScrewHalfPeriods S) : ℝ) else ⊤


/-- All spatial sets, including the reference helicoid and sets with
arbitrarily small periods, satisfy the infimum form of the cutoff. -/
theorem measured_physical_screw_infimum_cutoff (S : Set (Fin 3 → ℝ)) (η : ℝ) :
    (η : WithTop ℝ)≤physicalScrewHalfPeriod S ↔ HasNoScrewBelow η S := by
  classical
  by_cases present : (positiveScrewHalfPeriods S).Nonempty
  · rw [physicalScrewHalfPeriod,ite_eq_left present,WithTop.coe_le_coe]
    have bound : BddBelow (positiveScrewHalfPeriods S) := ⟨0,fun _ r => r.1.le⟩
    constructor
    · intro low r pos short symm
      exact short.not_ge (low.trans (csInf_le bound ⟨pos,symm⟩))
    · intro cut
      exact le_csInf present (fun r hr => le_of_not_gt fun short => cut r hr.1 short hr.2)
  · rw [physicalScrewHalfPeriod,ite_eq_right present]
    exact ⟨fun _ r pos _ symm => present ⟨r,pos,symm⟩,fun _ => le_top⟩

/-- At any strictly positive cutoff, a periodic image realizes its
measured half-period by an actual minimum. This uses only the screw
action and positive differences of symmetry steps. -/
theorem positive_cutoff_attains_measured_screw_period {S : Set (Fin 3 → ℝ)} {η : ℝ} (pos : 0<η)
    (cut : HasNoScrewBelow η S) (present : (positiveScrewHalfPeriods S).Nonempty) :
    ∃ k : ℝ, η≤k ∧ physicalScrewHalfPeriod S=(k : WithTop ℝ) ∧ IsLeast (positiveScrewHalfPeriods S) k := by
  classical
  have lower (r : ℝ) (hr : r∈positiveScrewHalfPeriods S) : η≤r :=
    le_of_not_gt fun short => cut r hr.1 short hr.2
  have subtract {s t : ℝ} (hs : s∈positiveScrewHalfPeriods S) (ht : t∈positiveScrewHalfPeriods S)
      (lt : s<t) : t-s∈positiveScrewHalfPeriods S := by
    refine ⟨sub_pos.mpr lt,?_⟩
    have compose : (unitHelicoidScrew (t-s) : _ → _) ∘ unitHelicoidScrew s=unitHelicoidScrew t := by
      funext p
      rw [Function.comp_apply,←unit_screw_add,sub_add_cancel]
    calc
      unitHelicoidScrew (t-s) '' S = unitHelicoidScrew (t-s) '' (unitHelicoidScrew s '' S) :=
        congrArg (fun V => unitHelicoidScrew (t-s) '' V) hs.2.symm
      _ = unitHelicoidScrew t '' S := by rw [←image_comp,compose]
      _ = S := ht.2
  have min := positive_difference_period_minimum pos present lower subtract
  exact ⟨sInf _,lower _ min.1,by rw [physicalScrewHalfPeriod,ite_eq_left present],min⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.measured_physical_screw_infimum_cutoff
#print axioms TwoAxisHelicoid.positive_cutoff_attains_measured_screw_period
