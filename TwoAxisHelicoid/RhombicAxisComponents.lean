import TwoAxisHelicoid.RhombicAxisRectangles

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Quotient projection identifies each cell with an open contractible
subset of the compact torus. Neither fixed axis meets those subsets. -/
theorem rhombic_axis_cell_topology {t : ℝ} (ht : 0 < t) (a : ℝ)
    (ha : a = -2 ∨ a = -1) :
    let U := rhombicAxisRectangle a t
    let f := fun z : U => periodTorusProjection (rhombicPeriodPair t ht) z.1
    IsOpenEmbedding f ∧ ContractibleSpace (periodTorusProjection (rhombicPeriodPair t ht) '' U) := by
  let L := rhombicPeriodPair t ht
  let U := rhombicAxisRectangle a t
  let f := fun z : U => periodTorusProjection L z.1
  have bounds {z : ℂ} (hz : z ∈ U) : z.re ∈ Ioo (-2:ℝ) 0 := by
    rcases ha with rfl | rfl <;> constructor <;> linarith [hz.1.1,hz.1.2]
  have hop : IsOpenMap (periodTorusProjection L) := QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
  have he : IsOpenEmbedding f := .of_continuous_injective_isOpenMap
    (QuotientAddGroup.continuous_mk.comp continuous_subtype_val)
    (fun x y h => Subtype.ext (rhombic_open_fundamental_inj ht (bounds x.2) x.2.2 (bounds y.2) y.2.2 h))
    (hop.comp (rhombicAxisRectangle_open a t).isOpenEmbedding_subtypeVal.isOpenMap)
  have hr : range f = periodTorusProjection L '' U := by
    ext q
    exact ⟨fun ⟨z,h⟩ => ⟨z.1,z.2,h⟩,fun ⟨z,hz,h⟩ => ⟨⟨z,hz⟩,h⟩⟩
  have cc := he.isEmbedding.toHomeomorph.contractibleSpace_iff.mp (rhombicAxisRectangle_contractible a ht)
  exact ⟨he,hr ▸ cc⟩

/-- The complement of the fixed curves has exactly two connected
components. Both are simply connected. -/
theorem rhombic_two_axis_complement_components {t : ℝ} (ht : 0 < t) :
    let L := rhombicPeriodPair t ht
    let A := periodTorusProjection L '' rhombicAxisRectangle (-2) t
    let B := periodTorusProjection L '' rhombicAxisRectangle (-1) t
    let C := {q : PeriodTorus L | rhombicHorizontalReflection ht q ≠ q ∧ rhombicVerticalReflection ht q ≠ q}
    C = A ∪ B ∧ Disjoint A B ∧ IsOpen A ∧ IsOpen B ∧ IsSimplyConnected A ∧ IsSimplyConnected B ∧
      (∀ q ∈ A, connectedComponentIn C q = A) ∧ ∀ q ∈ B, connectedComponentIn C q = B := by
  let L := rhombicPeriodPair t ht
  let A := periodTorusProjection L '' rhombicAxisRectangle (-2) t
  let B := periodTorusProjection L '' rhombicAxisRectangle (-1) t
  let C := {q : PeriodTorus L | rhombicHorizontalReflection ht q ≠ q ∧ rhombicVerticalReflection ht q ≠ q}
  have hC : C = A ∪ B := Set.ext (rhombic_off_axes_iff_rectangle ht)
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    rintro q ⟨z,hz,rfl⟩ ⟨w,hw,he⟩
    have e := rhombic_open_fundamental_inj ht
      (show z.re ∈ Ioo (-2:ℝ) 0 from ⟨hz.1.1,by linarith [hz.1.2]⟩) hz.2
      (show w.re ∈ Ioo (-2:ℝ) 0 from ⟨by linarith [hw.1.1],by linarith [hw.1.2]⟩) hw.2 he.symm
    subst w
    linarith [hz.1.2,hw.1.1]
  have hop : IsOpenMap (periodTorusProjection L) := QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
  have ha : IsOpen A := hop _ (rhombicAxisRectangle_open _ _)
  have hb : IsOpen B := hop _ (rhombicAxisRectangle_open _ _)
  let : ContractibleSpace A := (rhombic_axis_cell_topology ht (-2) (Or.inl rfl)).2
  let : ContractibleSpace B := (rhombic_axis_cell_topology ht (-1) (Or.inr rfl)).2
  have ca : IsSimplyConnected A := inferInstanceAs (SimplyConnectedSpace A)
  have cb : IsSimplyConnected B := inferInstanceAs (SimplyConnectedSpace B)
  have comp {P Q : Set (PeriodTorus L)} (he : C = P ∪ Q) (dis : Disjoint P Q)
      (hp : IsOpen P) (hq : IsOpen Q) (hc : IsSimplyConnected P) (q) (h : q ∈ P) :
      connectedComponentIn C q = P := by
    have hsub : P ⊆ C := by rw [he]; exact Set.subset_union_left
    apply Set.Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hp hq dis
        ((connectedComponentIn_subset C q).trans he.subset) ⟨q,mem_connectedComponentIn (hsub h),h⟩
    · exact hc.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn h hsub
  exact ⟨hC,hd,ha,hb,ca,cb,comp hC hd ha hb ca,comp (hC.trans (union_comm _ _)) hd.symm hb ha cb⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_two_axis_complement_components
