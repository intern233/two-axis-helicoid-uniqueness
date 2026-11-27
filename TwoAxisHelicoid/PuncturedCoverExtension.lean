import TwoAxisHelicoid.TorusSignCharacter

namespace TwoAxisHelicoid
open Set Topology

theorem puncturedLatticePlane_connectedSpace (L : PeriodPair) :
    ConnectedSpace (PuncturedLatticePlane L) :=
  isConnected_iff_connectedSpace.mp
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice)))

theorem puncturedLatticePlane_dense (L : PeriodPair) : Dense ((L.lattice : Set ℂ)ᶜ) :=
  Set.Countable.dense_compl ℝ (countable_of_Lindelof_of_discrete (X := L.lattice))

/-- A lift of the lattice projection on the punctured plane extends
uniquely through every lattice point when the target is an actual cover
of the whole compact torus. The extension is constructed using simple
connectedness of the plane and connectedness of its lattice complement. -/
theorem puncturedPlane_cover_lift_extends (L : PeriodPair)
    {E : Type*} [TopologicalSpace E] {p : E → PeriodTorus L} (hp : IsCoveringMap p)
    (f : C(PuncturedLatticePlane L,E))
    (hf : ∀ z, p (f z) = periodTorusProjection L z.1) :
    ∃! F : C(ℂ,E), (∀ z, p (F z) = periodTorusProjection L z) ∧
      ∀ z : PuncturedLatticePlane L, F z.1 = f z := by
  let z₀ : PuncturedLatticePlane L := puncturedBasisLine L 0 0
  let π : C(ℂ,PeriodTorus L) := ⟨periodTorusProjection L,QuotientAddGroup.continuous_mk⟩
  obtain ⟨F,⟨hF0,hFl⟩,_⟩ := hp.existsUnique_continuousMap_lifts π z₀.1 (f z₀) (hf z₀)
  let := puncturedLatticePlane_connectedSpace L
  have he : (fun z : PuncturedLatticePlane L => F z.1) = f := by
    apply hp.eq_of_comp_eq (F.continuous.comp continuous_subtype_val) f.continuous
      (funext fun z => (congrFun hFl z.1).trans (hf z).symm) z₀ hF0
  refine ⟨F,⟨fun z => congrFun hFl z,fun z => congrFun he z⟩,?_⟩
  intro G hG
  apply ContinuousMap.ext
  exact congrFun (hp.eq_of_comp_eq G.continuous F.continuous
    (funext fun z => (hG.1 z).trans (congrFun hFl z).symm) z₀.1
      ((hG.2 z₀).trans hF0.symm))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncturedPlane_cover_lift_extends
