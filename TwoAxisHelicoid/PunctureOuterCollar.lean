import TwoAxisHelicoid.ComplexEndCompactification

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology ContDiff Manifold

/-- The core charts can be restricted to an open region which covers
the complement of the end and meets the end only beyond radius s. -/
theorem PuncturedComplexEnd.outer_collar_open {M : Type*} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    (E : PuncturedComplexEnd M) {s : ℝ} (small : s<E.radius) :
    ∃ U : Set M, IsOpen U ∧ (∀ x : M, x∈U ∨ x∈E.coord.source) ∧
      ∀ x∈U, x∈E.coord.source → s<‖E.coord x‖ := by
  let K := E.filledChart.symm '' closedBall 0 s
  have within : closedBall (0:ℂ) s ⊆ E.filledChart.target := fun z h => lt_of_le_of_lt h small
  have compact : IsCompact K := (isCompact_closedBall (0:ℂ) s).image_of_continuousOn (E.filledChart.symm.continuousOn.mono within)
  let U := (OnePoint.some : M → OnePoint M) ⁻¹' Kᶜ
  refine ⟨U,compact.isClosed.isOpen_compl.preimage OnePoint.continuous_coe,?_,?_⟩
  · intro x
    by_cases h : x∈U
    · exact Or.inl h
    · have hx : (x:OnePoint M)∈K := not_not.mp h
      obtain ⟨z,hz,eqn⟩ := hx
      have mem := E.filledChart.map_target (within hz)
      rw [eqn] at mem
      change (x:OnePoint M)∉OnePoint.some '' E.coord.sourceᶜ at mem
      exact Or.inr (not_not.mp fun outside => mem ⟨x,outside,rfl⟩)
  · intro x hx dom
    by_contra! low
    have member : (x:OnePoint M)∈E.filledChart.source := by
      change (x:OnePoint M)∉OnePoint.some '' E.coord.sourceᶜ
      simpa only [OnePoint.coe_injective.mem_set_image,Set.mem_compl_iff,not_not] using dom
    exact hx ⟨E.coord x,by simpa only [mem_closedBall,dist_zero_right] using low,E.filledChart.left_inv member⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.PuncturedComplexEnd.outer_collar_open

