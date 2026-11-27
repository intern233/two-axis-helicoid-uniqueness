import TwoAxisHelicoid.ConnectedPlanarFrontier
import TwoAxisHelicoid.RegularBoundaryManifold
import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Set Metric Topology

private theorem compact_image_closure {A E : Type*} [TopologicalSpace A] [TopologicalSpace E] [T2Space E]
    {f : A → E} (cont : Continuous f) {U : Set A} (compact : IsCompact (closure U)) :
    f '' closure U=closure (f '' U) :=
  (image_closure_subset_closure_image cont).antisymm
    (closure_minimal (image_mono subset_closure) (compact.image cont).isClosed)

/-- Two relatively compact open patches with the same image under
embeddings also have exactly the same closed patch and boundary images.
The homeomorphism on closures respects membership in the open patches. -/
theorem compact_chart_patch_correspondence {A B E : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace E] [T2Space E] {f : A → E} {g : B → E} (ef : IsEmbedding f) (eg : IsEmbedding g)
    {U : Set A} {V : Set B} (ou : IsOpen U) (ov : IsOpen V) (ku : IsCompact (closure U))
    (kv : IsCompact (closure V)) (same : f '' U=g '' V) :
    (∃ H : closure U ≃ₜ closure V, ∀ q, f q.1=g (H q).1 ∧ (q.1∈U ↔ (H q).1∈V)) ∧
      ∃ h : frontier U ≃ₜ frontier V, ∀ q, f q.1=g (h q).1 := by
  have closures : f '' closure U=g '' closure V := by
    rw [compact_image_closure ef.continuous ku,compact_image_closure eg.continuous kv,same]
  have frontiers : f '' frontier U=g '' frontier V := by
    rw [frontier,frontier,ou.interior_eq,ov.interior_eq,Set.image_sdiff ef.injective,Set.image_sdiff eg.injective,closures,same]
  have transport {S : Set A} {T : Set B} (eq : f '' S=g '' T) :
      ∃ H : S ≃ₜ T, ∀ q, f q.1=g (H q).1 := by
    let F := ef.homeomorphImage S
    let G := eg.homeomorphImage T
    let H := (F.trans (Homeomorph.setCongr eq)).trans G.symm
    refine ⟨H,fun q => ?_⟩
    have val := congrArg Subtype.val (G.apply_symm_apply ((Homeomorph.setCongr eq) (F q)))
    exact val.symm
  obtain ⟨H,value⟩ := transport closures
  refine ⟨⟨H,fun q => ⟨value q,?_⟩⟩,transport frontiers⟩
  calc q.1∈U ↔ f q.1∈f '' U := ef.injective.mem_set_image.symm
       _ ↔ g (H q).1∈g '' V := by rw [value,same]
       _ ↔ (H q).1∈V := eg.injective.mem_set_image

/-- The sphere-complement condition and the actual regular charts on the
surface give a single compact, connected real one-manifold as boundary in
the common plane chart, together with the homeomorphism of its filled patch. -/
theorem bounded_planar_cut_boundary_model {M E : Type*} [TopologicalSpace M] [TopologicalSpace E] [T2Space E]
    {j : ℂ → E} {i : M → E} (ej : IsEmbedding j) (ei : IsEmbedding i)
    {W : Set ℂ} {V : Set M} (ow : IsOpen W) (cw : IsConnected W) (kw : IsCompact (closure W))
    (sphere : IsPreconnected ((OnePoint.some : ℂ → OnePoint ℂ) '' W)ᶜ)
    (ov : IsOpen V) (kv : IsCompact (closure V)) (same : j '' W=i '' V)
    (regular : ∀ q∈frontier V, ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      q∈e.source ∧ e.IsImage (frontier V) ({0} ×ˢ (univ : Set ℝ))) :
    IsConnected (frontier W) ∧ IsCompact (frontier W) ∧ Nonempty (ChartedSpace ℝ (frontier W)) ∧
      ∃ H : closure W ≃ₜ closure V, ∀ q, j q.1=i (H q).1 ∧ (q.1∈W ↔ (H q).1∈V) := by
  obtain ⟨fill,h,loc⟩ := compact_chart_patch_correspondence ej ei ow ov kw kv same
  obtain ⟨⟨S⟩,_,_⟩ := compact_regular_frontier_is_finite_manifold kv regular
  have charts : Nonempty (ChartedSpace ℝ (frontier W)) := by
    let _ := S
    exact ⟨h.symm.chartedSpace⟩
  have proper : W≠univ := fun eq => noncompact_univ ℂ (by simpa only [eq,closure_univ] using kw)
  exact ⟨⟨nonempty_frontier_iff.mpr ⟨cw.nonempty,proper⟩,
    connected_open_plane_frontier ow cw.isPreconnected (plane_complement_of_spherical_complement ow kw sphere)⟩,
    kw.of_isClosed_subset isClosed_frontier frontier_subset_closure,charts,fill⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_chart_patch_correspondence
#print axioms TwoAxisHelicoid.bounded_planar_cut_boundary_model
