import TwoAxisHelicoid.ReferenceHelicoidEnd
import TwoAxisHelicoid.ConicalHelicoidTube
import TwoAxisHelicoid.OriginalPositionalHelicoid

namespace TwoAxisHelicoid
open Complex Filter Set Metric Topology
open scoped Topology

/-- The given one-sided positional asymptote, even at signed pitch,
gives actual signed normal fibers on every sufficiently distant subend. -/
theorem positional_standard_end_actual_tubes {M : Type*} [TopologicalSpace M] {X : M → Fin 3 → ℝ}
    (proper : IsProperMap X) (approach : ApproachesSetAtInfinity (range X) (range (fun z : ℂ => standardHelicoid z.re z.im))) :
    ∀ ε : ℝ, 0<ε → ∃ U : Set M, IsCompact Uᶜ ∧ ∀ q∈U,
      ∃ s r θ : ℝ, |s|<ε ∧ coordinateToTube (X q)=helicoidTubeMap ((s,r),θ) := by
  intro ε he
  let κ := min (ε/2) (1/2)
  have kp : 0<κ := lt_min (half_pos he) (by norm_num)
  have small : κ<1 := (min_le_right _ _).trans_lt (by norm_num)
  have ke : κ<ε := (min_le_left _ _).trans_lt (half_lt_self he)
  obtain ⟨B,bound⟩ := approach (κ/2) (half_pos kp)
  let K := X ⁻¹' closedBall 0 B
  have ck : IsCompact K := proper.isCompact_preimage (isCompact_closedBall _ _)
  refine ⟨Kᶜ,by simpa only [compl_compl] using ck,?_⟩
  intro q hq
  have far : B<‖X q‖ := by
    change X q∉closedBall 0 B at hq
    simpa only [mem_closedBall,dist_zero_right,not_le] using hq
  obtain ⟨_,⟨z,rfl⟩,near⟩ := bound _ (mem_range_self q) far.le
  have each (j : Fin 3) : (X q j-standardHelicoid z.re z.im j)^2≤(κ/2)^2 := by
    rw [dist_eq_norm] at near
    have c := (norm_le_pi_norm (X q-standardHelicoid z.re z.im) j).trans near.le
    rw [Pi.sub_apply,Real.norm_eq_abs] at c
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (half_pos kp).le).mpr c
  have hd : helicoidSquaredDistance (X q 0,X q 1,X q 2) z.re z.im≤κ^2 := by
    have a := each 0
    have b := each 1
    have c := each 2
    change (X q 0-z.re*Real.cos z.im)^2≤_ at a
    change (X q 1-z.re*Real.sin z.im)^2≤_ at b
    change (X q 2-z.im)^2≤_ at c
    unfold helicoidSquaredDistance
    nlinarith [sq_nonneg κ]
  let y := coordinateToTube (X q)
  obtain ⟨inside,height⟩ := helicoid_tube_of_squared_distance_le (y := y) kp.le small ⟨z.re,z.im,hd⟩
  let v := helicoidTubeEquiv.symm y
  exact ⟨v.1.1,v.1.2,v.2,height.trans_lt ke,(helicoidTubeEquiv.right_inv inside).symm⟩

theorem reference_frame_positional_standard {M : Type*} (X : M → Fin 3 → ℝ) {α : ℝ} (ha : α≠0)
    (pos : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0))) :
    ApproachesSetAtInfinity (range (centeredHelicoidNormalization ha ∘ X))
      (range (fun z : ℂ => standardHelicoid z.re z.im)) := by
  let R := centeredHelicoidNormalization ha
  have hz : (![0,0,0] : Fin 3 → ℝ)=0 := by ext j; fin_cases j <;> rfl
  have std : range (fun z : ℂ => standardHelicoid z.re z.im)=R '' range (axisRuledHelicoid I α 0) := by
    have eq := inverse_image_standardHelicoid_axisNormalization ha 0
    rw [hz] at eq
    change R ⁻¹' range (fun z : ℂ => standardHelicoid z.re z.im)=_ at eq
    rw [← eq,image_preimage_eq _ R.surjective]
  rw [std,range_comp]
  simpa only [zero_add] using (ApproachesSetAtInfinity.affine_equiv _ _ R 0).mpr pos

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_standard_end_actual_tubes
