import TwoAxisHelicoid.BoundedSmoothODE

namespace TwoAxisHelicoid
open Set Metric
open scoped Topology NNReal

/-- Two trajectories of the same smooth autonomous field which meet at
any time in the closed interval have identical restrictions to it. -/
theorem smooth_field_unit_trajectory_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {V : E → E} (smooth : ContDiff ℝ 1 V) {γ η : ℝ → E}
    (dγ : ∀ t∈Icc (0:ℝ) 1, HasDerivAt γ (V (γ t)) t)
    (dη : ∀ t∈Icc (0:ℝ) 1, HasDerivAt η (V (η t)) t)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) (meet : γ s=η s) : EqOn γ η (Icc (0:ℝ) 1) := by
  have cγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht => (dγ t ht).continuousAt.continuousWithinAt
  have cη : ContinuousOn η (Icc (0:ℝ) 1) := fun t ht => (dη t ht).continuousAt.continuousWithinAt
  obtain ⟨R,inside⟩ := ((isCompact_Icc.image_of_continuousOn cγ).union
    (isCompact_Icc.image_of_continuousOn cη)).isBounded.subset_closedBall (0:E)
  obtain ⟨K,lip⟩ := smooth.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall (0:E) R)
    (isCompact_closedBall (0:E) R)
  have left : EqOn γ η (Icc 0 s) := by
    apply ODE_solution_unique_of_mem_Icc_left (v := fun _ => V) (s := fun _ => closedBall (0:E) R)
      (fun _ _ => lip) (cγ.mono (Icc_subset_Icc_right hs.2)) _ _ (cη.mono (Icc_subset_Icc_right hs.2)) _ _ meet
    all_goals intro t ht
    all_goals have h : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.trans hs.2⟩
    · exact (dγ t h).hasDerivWithinAt
    · exact inside (Or.inl (mem_image_of_mem γ h))
    · exact (dη t h).hasDerivWithinAt
    · exact inside (Or.inr (mem_image_of_mem η h))
  have right : EqOn γ η (Icc s 1) := by
    apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => V) (s := fun _ => closedBall (0:E) R)
      (fun _ _ => lip) (cγ.mono (Icc_subset_Icc_left hs.1)) _ _ (cη.mono (Icc_subset_Icc_left hs.1)) _ _ meet
    all_goals intro t ht
    all_goals have h : t∈Icc (0:ℝ) 1 := ⟨hs.1.trans ht.1,ht.2.le⟩
    · exact (dγ t h).hasDerivWithinAt
    · exact inside (Or.inl (mem_image_of_mem γ h))
    · exact (dη t h).hasDerivWithinAt
    · exact inside (Or.inr (mem_image_of_mem η h))
  intro t ht
  rcases le_total t s with h|h
  · exact left ⟨ht.1,h⟩
  · exact right ⟨h,ht.2⟩

/-- A smooth trajectory cannot strike a stationary point in finite time
when its initial point is outside the stationary set. -/
theorem smooth_field_trajectory_avoids_fixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {V : E → E} (smooth : ContDiff ℝ 1 V) {γ : ℝ → E}
    (ode : ∀ t∈Icc (0:ℝ) 1, HasDerivAt γ (V (γ t)) t)
    {S : Set E} (fixed : ∀ p∈S,V p=0) (initial : γ 0∉S) :
    ∀ t∈Icc (0:ℝ) 1, γ t∉S := by
  intro t ht hit
  let η := fun _ : ℝ => γ t
  have dη (s : ℝ) (_hs : s∈Icc (0:ℝ) 1) : HasDerivAt η (V (η s)) s := by
    change HasDerivAt (fun _ : ℝ => γ t) (V (γ t)) s
    rw [fixed _ hit]
    exact hasDerivAt_const _ _
  have eq := smooth_field_unit_trajectory_unique smooth ode dη ht (show γ t=η t from rfl)
  exact initial ((eq (left_mem_Icc.mpr zero_le_one)) ▸ hit)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_field_trajectory_avoids_fixed
