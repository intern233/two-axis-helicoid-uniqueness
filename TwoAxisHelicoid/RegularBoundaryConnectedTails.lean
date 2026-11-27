import TwoAxisHelicoid.ExteriorHeightEscape
import TwoAxisHelicoid.RegularBallComponentBoundary

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology

/-- A neighborhood assembled from connected interior sides of a connected
frontier has connected intersection with the domain. Two patches meeting
at a frontier point always meet on the interior as well. -/
private theorem connected_union_boundary_sides {X : Type*} [TopologicalSpace X] {W : Set X}
    (front : IsPreconnected (frontier W)) (O : frontier W → Set X)
    (opened : ∀ i, IsOpen (O i)) (own : ∀ i, i.1∈O i)
    (side : ∀ i, IsPreconnected (O i ∩ W)) : IsPreconnected ((⋃ i, O i) ∩ W) := by
  classical
  let T := (⋃ i, O i) ∩ W
  have incl (i : frontier W) : O i ∩ W ⊆ T := fun x ⟨xo,xw⟩ => ⟨mem_iUnion.mpr ⟨i,xo⟩,xw⟩
  apply isPreconnected_iff_subset_of_disjoint.mpr
  intro A B oa ob cover disj
  have exclude (x : X) (xt : x∈T) (xa : x∈A) (xb : x∈B) : False :=
    eq_empty_iff_forall_notMem.mp disj x ⟨xt,xa,xb⟩
  have either (i : frontier W) : O i ∩ W ⊆ A ∨ O i ∩ W ⊆ B :=
    isPreconnected_iff_subset_of_disjoint.mp (side i) _ _ oa ob ((incl i).trans cover)
      (eq_empty_iff_forall_notMem.mpr fun x ⟨xi,xa,xb⟩ => exclude x (incl i xi) xa xb)
  let N := fun S : Set X => ⋃ i : {i : frontier W // O i ∩ W ⊆ S}, O i.1
  have on (S : Set X) : IsOpen (N S) := isOpen_iUnion fun i => opened i.1
  have center (i : frontier W) {S : Set X} (hs : O i ∩ W ⊆ S) : i.1∈N S :=
    mem_iUnion.mpr ⟨⟨i,hs⟩,own i⟩
  have none (x : X) (fx : x∈frontier W) (a : x∈N A) (b : x∈N B) : False := by
    obtain ⟨i,ia⟩ := mem_iUnion.mp a
    obtain ⟨j,jb⟩ := mem_iUnion.mp b
    obtain ⟨z,⟨zi,zj⟩,zw⟩ := mem_closure_iff.mp (frontier_subset_closure fx) (O i.1 ∩ O j.1)
      ((opened i.1).inter (opened j.1)) ⟨ia,jb⟩
    exact exclude z (incl i.1 ⟨zi,zw⟩) (i.2 ⟨zi,zw⟩) (j.2 ⟨zj,zw⟩)
  have fc : frontier W ⊆ N A ∪ N B := by
    intro x hx
    let i : frontier W := ⟨x,hx⟩
    exact (either i).imp (center i) (center i)
  rcases isPreconnected_iff_subset_of_disjoint.mp front _ _ (on A) (on B) fc
      (eq_empty_iff_forall_notMem.mpr fun x ⟨h,a,b⟩ => none x h a b) with allA|allB
  · left
    rintro x ⟨xo,xw⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp xo
    rcases either i with a|b
    · exact a ⟨hi,xw⟩
    · exact (none i.1 i.2 (allA i.2) (center i b)).elim
  · right
    rintro x ⟨xo,xw⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp xo
    rcases either i with a|b
    · exact (none i.1 i.2 (center i a) (allB i.2)).elim
    · exact b ⟨hi,xw⟩

/-- A relatively compact open domain with a connected, locally one-sided
boundary has only one end. The compact complementary core is in the
domain itself. -/
theorem domain_connected_tails_of_boundary_sides {X : Type*} [TopologicalSpace X] [T2Space X]
    {W : Set X} (op : IsOpen W) (kw : IsCompact (closure W)) (front : IsPreconnected (frontier W))
    (patch : ∀ x∈frontier W, ∀ G : Set X, IsOpen G → x∈G →
      ∃ O : Set X, IsOpen O ∧ x∈O ∧ O⊆G ∧ IsPreconnected (O ∩ W)) : HasConnectedCompactTails W := by
  classical
  intro K compact
  let C := (Subtype.val : W → X) '' K
  have cc : IsClosed C := (compact.image continuous_subtype_val).isClosed
  have avail (i : frontier W) : ∃ O : Set X, IsOpen O ∧ i.1∈O ∧ O⊆Cᶜ ∧ IsPreconnected (O ∩ W) := by
    apply patch _ i.2 _ cc.isOpen_compl
    rintro ⟨q,_,eq⟩
    exact i.2.2 (op.interior_eq.symm ▸ (eq ▸ q.2))
  choose O opened own sub side using avail
  let P := ⋃ i, O i
  have openP : IsOpen P := isOpen_iUnion opened
  have frontP : frontier W ⊆ P := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,own ⟨x,hx⟩⟩
  let U := (Subtype.val : W → X) ⁻¹' P
  have imageU : (Subtype.val : W → X) '' U=P∩W := (Subtype.image_preimage_coe W P).trans (inter_comm W P)
  refine ⟨U,Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    (imageU.symm ▸ connected_union_boundary_sides front O opened own side),?_,?_⟩
  · apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have eq : (Subtype.val : W → X) '' Uᶜ=closure W ∩ Pᶜ := by
      ext x
      constructor
      · rintro ⟨q,qo,rfl⟩
        exact ⟨subset_closure q.2,qo⟩
      · rintro ⟨cl,outside⟩
        have wx : x∈W := by
          by_contra miss
          exact outside (frontP ⟨cl,fun h => miss (interior_subset h)⟩)
        exact ⟨⟨x,wx⟩,outside,rfl⟩
    rw [eq]
    exact kw.inter_right openP.isClosed_compl
  · apply disjoint_left.mpr
    intro q inside hit
    obtain ⟨i,hi⟩ := mem_iUnion.mp (show q.1∈P from inside)
    exact sub i hi (mem_image_of_mem _ hit)

/-- A real regular cut yields connected interior sides in arbitrarily
small prescribed ambient open patches. -/
theorem boundary_half_plane_has_connected_sides {X : Type*} [TopologicalSpace X] {W : Set X}
    {x : X} (e : OpenPartialHomeomorph X (ℝ × ℝ)) (hx : x∈e.source)
    (side : e.IsImage W (Iio (0:ℝ) ×ˢ univ)) {G : Set X} (og : IsOpen G) (xg : x∈G) :
    ∃ O : Set X, IsOpen O ∧ x∈O ∧ O⊆G ∧ IsPreconnected (O ∩ W) := by
  let V := e '' (e.source ∩ G)
  have vo : IsOpen V := e.isOpen_image_of_subset_source (e.open_source.inter og) inter_subset_left
  have xv : e x∈V := mem_image_of_mem _ ⟨hx,xg⟩
  obtain ⟨r,rp,small⟩ := Metric.mem_nhds_iff.mp (vo.mem_nhds xv)
  let B := ball (e x) r
  have target : B⊆e.target := by
    intro y hy
    obtain ⟨w,hw,rfl⟩ := small hy
    exact e.map_source hw.1
  let O := e.source ∩ e ⁻¹' B
  refine ⟨O,e.isOpen_inter_preimage isOpen_ball,⟨hx,mem_ball_self rp⟩,?_,?_⟩
  · rintro w ⟨ws,wb⟩
    obtain ⟨y,hy,eq⟩ := small wb
    exact e.injOn hy.1 ws eq ▸ hy.2
  · have val : e.symm '' (B∩(Iio (0:ℝ) ×ˢ univ))=O∩W := by
      ext y
      constructor
      · rintro ⟨z,⟨zb,zh⟩,rfl⟩
        exact ⟨⟨e.map_target (target zb),by change e (e.symm z)∈B; rwa [e.right_inv (target zb)]⟩,
          (side.symm_apply_mem_iff (target zb)).mpr zh⟩
      · rintro ⟨⟨ys,yb⟩,yw⟩
        exact ⟨e y,⟨yb,(side ys).mpr yw⟩,e.left_inv ys⟩
    rw [← val]
    exact ((convex_ball (e x) r).inter ((convex_Iio _).prod convex_univ)).isPreconnected.image _
      (e.continuousOn_symm.mono fun _ h => target h.1)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.domain_connected_tails_of_boundary_sides
#print axioms TwoAxisHelicoid.boundary_half_plane_has_connected_sides
