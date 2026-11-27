import TwoAxisHelicoid.RegularBallComponentBoundary
import Mathlib.Geometry.Manifold.ChartedSpace

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- The second coordinate of a regular plane cut gives a chart on its
actual frontier with the induced topology. -/
theorem line_chart_on_slice {M : Type*} [TopologicalSpace M] {S : Set M}
    (q : S) (e : OpenPartialHomeomorph M (ℝ × ℝ)) (hq : q.1∈e.source)
    (line : e.IsImage S ({0} ×ˢ (univ : Set ℝ))) :
    ∃ a : OpenPartialHomeomorph S ℝ, q∈a.source ∧ ∀ x∈a.source, a x=(e x.1).2 := by
  classical
  let L : ℝ → ℝ × ℝ := fun t => (0,t)
  have cL : Continuous L := continuous_const.prodMk continuous_id
  let U := (Subtype.val : S → M) ⁻¹' e.source
  let V := L ⁻¹' e.target
  let f : S → ℝ := fun x => (e x.1).2
  let g : ℝ → S := fun t => if h : e.symm (L t)∈S then ⟨_,h⟩ else q
  have lift (t : ℝ) (h : t∈V) : (g t).1=e.symm (L t) := by
    have hs := (line.symm_apply_mem_iff h).mpr (show L t∈({0}:Set ℝ) ×ˢ univ from ⟨rfl,mem_univ _⟩)
    simp [g,hs]
  have coords (x : S) (hx : x∈U) : L (f x)=e x.1 :=
    Prod.ext ((line hx).mpr x.2).1.symm rfl
  let a : OpenPartialHomeomorph S ℝ := {
    toFun := f
    invFun := g
    source := U
    target := V
    map_source' := fun x hx => show L (f x)∈e.target from (coords x hx).symm ▸ e.map_source hx
    map_target' := fun t ht => show (g t).1∈e.source from (lift t ht).symm ▸ e.map_target ht
    left_inv' := fun x hx => by
      apply Subtype.ext
      have hv : f x∈V := show L (f x)∈e.target from (coords x hx).symm ▸ e.map_source hx
      rw [lift _ hv,coords x hx,e.left_inv hx]
    right_inv' := fun t ht => by
      change (e (g t).1).2=t
      rw [lift _ ht,e.right_inv ht]
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage cL
    continuousOn_toFun := continuous_snd.continuousOn.comp
      (e.continuousOn.comp continuous_subtype_val.continuousOn fun _ h => h) (mapsTo_univ _ _)
    continuousOn_invFun := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      apply continuous_induced_rng.mpr
      exact (continuousOn_iff_continuous_domRestrict.mp
        (e.continuousOn_symm.comp cL.continuousOn (show MapsTo L V e.target from fun _ h => h))).congr
          fun t => (lift t.1 t.2).symm }
  exact ⟨a,hq,fun _ _ => rfl⟩

/-- A compact regular frontier is an actual compact real
one-manifold, with finitely many connected components. -/
theorem compact_regular_frontier_is_finite_manifold {M : Type*} [TopologicalSpace M] {V : Set M}
    (compact : IsCompact (closure V))
    (regular : ∀ q∈frontier V, ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      q∈e.source ∧ e.IsImage (frontier V) ({0} ×ˢ (univ : Set ℝ))) :
    Nonempty (ChartedSpace ℝ (frontier V)) ∧ IsCompact (frontier V) ∧ Finite (ConnectedComponents (frontier V)) := by
  classical
  have point (q : frontier V) : ∃ a : OpenPartialHomeomorph (frontier V) ℝ, q∈a.source := by
    obtain ⟨e,hq,line⟩ := regular q q.2
    obtain ⟨a,qa,_⟩ := line_chart_on_slice q e hq line
    exact ⟨a,qa⟩
  choose a source using point
  let atlas : ChartedSpace ℝ (frontier V) := ⟨range a,a,source,mem_range_self⟩
  have cf := compact.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let _ := atlas
  let _ : CompactSpace (frontier V) := isCompact_iff_compactSpace.mp cf
  let _ : LocallyConnectedSpace (frontier V) := ChartedSpace.locallyConnectedSpace ℝ _
  exact ⟨⟨atlas⟩,cf,inferInstance⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.line_chart_on_slice
#print axioms TwoAxisHelicoid.compact_regular_frontier_is_finite_manifold
