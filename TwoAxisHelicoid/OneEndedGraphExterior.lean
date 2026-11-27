module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.Order.Compact

public section

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- An exterior chart on a one-ended surface can be restricted over any
sufficiently distant sphere while retaining a compact complementary core.
A single family on which both a physical observable and the chart radius
are unbounded suffices to distinguish the two sides of the sphere. -/
theorem one_ended_chart_exterior_mem_cocompact {M B L : Type*}
    [TopologicalSpace M] [TopologicalSpace B] [LinearOrder L] [TopologicalSpace L]
    [OrderTopology L] [NoMaxOrder L] [Nonempty L]
    (tails : ∀ K : Set M, IsCompact K →
      ∃ U : Set M, IsPreconnected U ∧ IsCompact Uᶜ ∧ Disjoint U K)
    (e : OpenPartialHomeomorph M B) (radius : B → L) (contRadius : Continuous radius)
    (levels : ∀ t : L, IsCompact {p | radius p = t})
    {r : L} (outer : {q : B | r < radius q} ⊆ e.target) (core : IsCompact e.sourceᶜ)
    (h : M → L) (cont : Continuous h)
    (escape : ∀ A : L, ∃ x ∈ e.source, A < h x ∧ A < radius (e x)) (R : L) :
    ∀ᶠ x in cocompact M, x ∈ e.source ∧ R < radius (e x) := by
  obtain ⟨ρ,larger⟩ := exists_gt (max R r)
  have hr : r < ρ := (le_max_right R r).trans_lt larger
  have hR : R < ρ := (le_max_left R r).trans_lt larger
  have sphereTarget : {p | radius p = ρ} ⊆ e.target := by
    intro p hp
    exact outer (show r < radius p from (hp : radius p = ρ).symm ▸ hr)
  let C := e.symm '' {p | radius p = ρ}
  have compact : IsCompact C :=
    (levels ρ).image_of_continuousOn (e.symm.continuousOn.mono sphereTarget)
  obtain ⟨U,connected,compactOutside,avoids⟩ := tails _ (core.union compact)
  have src (x : M) (hx : x ∈ U) : x ∈ e.source := by
    by_contra absent
    exact disjoint_left.mp avoids hx (Or.inl absent)
  have avoidsSphere (x : M) (hx : x ∈ U) : radius (e x) ≠ ρ := by
    intro eq
    apply disjoint_left.mp avoids hx (Or.inr ?_)
    exact ⟨e x,eq,e.left_inv (src x hx)⟩
  let T := (fun x => radius (e x)) '' U
  have rangeConn : IsPreconnected T := connected.image _ ((contRadius.comp_continuousOn e.continuousOn).mono (fun x hx => src x hx))
  have sides : T ⊆ Iio ρ ∪ Ioi ρ := by
    rintro _ ⟨x,hx,rfl⟩
    exact lt_or_gt_of_ne (avoidsSphere x hx)
  obtain ⟨H,upper⟩ := compactOutside.bddAbove_image cont.continuousOn
  obtain ⟨p,_,high,far⟩ := escape (max H ρ)
  have inTail : p ∈ U := by
    by_contra absent
    exact ((le_max_left H ρ).trans_lt high).not_ge (upper (mem_image_of_mem h absent))
  rcases rangeConn.subset_or_subset isOpen_Iio isOpen_Ioi
      (disjoint_left.mpr fun _ low big => (low : _ < ρ).asymm big) sides with low | big
  · exact ((low (mem_image_of_mem _ inTail) : radius (e p) < ρ).asymm ((le_max_right H ρ).trans_lt far)).elim
  · have ev : U ∈ cocompact M := by simpa only [compl_compl] using compactOutside.compl_mem_cocompact
    exact Filter.mem_of_superset ev fun p hp =>
      ⟨src p hp,hR.trans (big (mem_image_of_mem _ hp) : ρ < radius (e p))⟩

/-- Restriction of an actual partial homeomorphism over an open exterior.
Its inverse still takes each base point to the original surface point. -/
theorem exists_restricted_exterior_homeomorph {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
    (e : OpenPartialHomeomorph M B) {T : Set B} (outer : T ⊆ e.target) :
    ∃ F : (e.source ∩ e ⁻¹' T : Set M) ≃ₜ T, ∀ p, (F.symm p).1 = e.symm p.1 := by
  let D := e.source ∩ e ⁻¹' T
  let F : D ≃ₜ T :=
    { toFun := fun x => ⟨e x.1,x.2.2⟩
      invFun := fun p => ⟨e.symm p.1,e.map_target (outer p.2),by
        change e (e.symm p.1) ∈ T
        rw [e.right_inv (outer p.2)]
        exact p.2⟩
      left_inv := fun x => Subtype.ext (e.left_inv x.2.1)
      right_inv := fun p => Subtype.ext (e.right_inv (outer p.2))
      continuous_toFun := Continuous.subtype_mk (continuous_iff_continuousAt.mpr fun x : D =>
        (e.continuousAt x.2.1).comp continuous_subtype_val.continuousAt) _
      continuous_invFun := Continuous.subtype_mk (continuous_iff_continuousAt.mpr fun p : T =>
        (e.symm.continuousAt (outer p.2)).comp continuous_subtype_val.continuousAt) _ }
  exact ⟨F,fun _ => rfl⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.one_ended_chart_exterior_mem_cocompact
#print axioms TwoAxisHelicoid.exists_restricted_exterior_homeomorph
