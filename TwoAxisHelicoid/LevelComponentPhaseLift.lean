import TwoAxisHelicoid.CircleLiftNeighborhood

namespace TwoAxisHelicoid
open Set Topology

theorem PhaseLiftsOn.clopen_union {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {φ : X → Circle} {A B : Set X} (a : PhaseLiftsOn φ A) (b : PhaseLiftsOn φ B)
    (ca : IsClopen A) (cb : IsClosed B) : PhaseLiftsOn φ (A∪B) := by
  have h := a.disjoint_union (b.mono (sdiff_subset (s:=B) (t:=A))) ca.isClosed
    (cb.sdiff ca.isOpen) (Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx))
  apply h.mono
  intro x hx
  by_cases xa : x∈A
  · exact Or.inl xa
  · exact Or.inr ⟨hx.resolve_left xa,xa⟩

/-- An angle on each connected component of a compact Hausdorff space
gives an angle on the entire space. Compactness is applied first to
clopen neighborhoods of one component, then to a cover of all points. -/
theorem phase_lift_of_component_lifts {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {φ : X → Circle} (cφ : Continuous φ)
    (each : ∀ x : X, ∃ u : C(connectedComponent x,ℝ), ∀ q, normalizedPhase (u q)=φ q) :
    PhaseLiftsOn φ univ := by
  classical
  have localLift (x : X) : ∃ V : Set X, IsClopen V ∧ x∈V ∧ PhaseLiftsOn φ V := by
    obtain ⟨u,hu⟩ := each x
    obtain ⟨O,op,sub,lift⟩ := phase_lifts_in_a_neighborhood cφ isClosed_connectedComponent u hu
    obtain ⟨V,cl,hx,hv⟩ := clopen_inside_component_neighborhood x op sub
    exact ⟨V,cl,hx,lift.mono hv⟩
  choose V cl own lifts using localLift
  obtain ⟨t,cover⟩ := isCompact_univ.elim_finite_subcover V (fun x => (cl x).isOpen)
    (fun x _ => mem_iUnion.mpr ⟨x,own x⟩)
  have finiteLift (s : Finset X) : PhaseLiftsOn φ (⋃ i∈s,V i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0,by simp⟩
    | @insert i s _ ih =>
      rw [Finset.set_biUnion_insert]
      exact (lifts i).clopen_union ih (cl i) (isClosed_biUnion_finset (fun j _ => (cl j).isClosed))
  exact (finiteLift t).mono cover

/-- When the phase lifts on every component of a compact level, it
lifts on the inverse image of an open neighborhood of that level value.
The continuous real function realizing the lift is defined globally. -/
theorem height_neighborhood_phase_lift {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] {h : X → Y} (ch : Continuous h)
    {φ : X → Circle} (cφ : Continuous φ) (t : Y)
    (each : ∀ x : h ⁻¹' {t}, ∃ u : C(connectedComponent x,ℝ), ∀ q, normalizedPhase (u q)=φ q.1.1) :
    ∃ I : Set Y, IsOpen I ∧ t∈I ∧ PhaseLiftsOn φ (h ⁻¹' I) := by
  let D := h ⁻¹' {t}
  have cd : IsClosed D := isClosed_singleton.preimage ch
  let _ : CompactSpace D := isCompact_iff_compactSpace.mp cd.isCompact
  obtain ⟨f,hf⟩ := phase_lift_of_component_lifts (cφ.comp (continuous_subtype_val (p:=fun x => x∈D))) each
  obtain ⟨O,op,sub,lift⟩ := phase_lifts_in_a_neighborhood cφ cd f (fun q => hf q (mem_univ _))
  refine ⟨(h '' Oᶜ)ᶜ,(ch.isClosedMap _ op.isClosed_compl).isOpen_compl,?_,lift.mono ?_⟩
  · rintro ⟨x,hx,eq⟩
    exact hx (sub eq)
  · intro x hx
    by_contra no
    exact hx ⟨x,no,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_neighborhood_phase_lift
