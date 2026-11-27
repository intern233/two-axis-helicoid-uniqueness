import TwoAxisHelicoid.PlanarPatchDiskParameter
import TwoAxisHelicoid.HalfPlaneCayleyLimit
import TwoAxisHelicoid.ClosedDiskParameterFibers

namespace TwoAxisHelicoid
open Set Metric Topology

/-- A relatively compact planar cut with connected spherical complement
and actual local half-plane charts is a closed disk, including its
identified interior. This constructs the disk by holomorphic
parametrization and proves its boundary correspondence. -/
theorem regular_planar_patch_closed_disk {M E : Type*} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace E] [T2Space E] {j : ℂ → E} {i : M → E} (ej : IsOpenEmbedding j) (ei : IsOpenEmbedding i)
    {W : Set ℂ} {V : Set M} (ow : IsOpen W) (cw : IsConnected W) (kw : IsCompact (closure W))
    (sphere : IsPreconnected ((OnePoint.some : ℂ → OnePoint ℂ) '' W)ᶜ)
    (ov : IsOpen V) (kv : IsCompact (closure V)) (same : j '' W=i '' V)
    (regular : ∀ q∈frontier V, ∃ e : OpenPartialHomeomorph M (ℝ×ℝ), q∈e.source ∧ e.IsImage V (Iio 0 ×ˢ univ)) :
    ∃ D : closedBall (0:ℂ) 1 ≃ₜ closure V, ∀ z, z.1∈ball (0:ℂ) 1 ↔ (D z).1∈V := by
  obtain ⟨⟨H,values⟩,F,front⟩ := compact_chart_patch_correspondence ej.isEmbedding ei.isEmbedding ow ov kw kv same
  have conn := connected_open_plane_frontier ow cw.isPreconnected (plane_complement_of_spherical_complement ow kw sphere)
  let _ : PreconnectedSpace (frontier W) := isPreconnected_iff_preconnectedSpace.mp conn
  have cv : IsPreconnected (frontier V) := by
    have src : IsPreconnected (univ : Set (frontier W)) := isPreconnected_univ
    have img := src.image F F.continuous.continuousOn
    rw [image_univ,F.surjective.range_eq] at img
    exact isPreconnected_iff_preconnectedSpace.mpr ⟨img⟩
  have vt := domain_connected_tails_of_boundary_sides ov kv cv (by
    intro q h G og qg
    obtain ⟨e,qe,side⟩ := regular q h
    exact boundary_half_plane_has_connected_sides e qe side og qg)
  let h := ((ej.isEmbedding.homeomorphImage W).trans (Homeomorph.setCongr same)).trans (ei.isEmbedding.homeomorphImage V).symm
  have wt := connected_compact_tails_homeomorph h.symm vt
  have sides := plane_domain_closure_connected_sides ow (planar_model_has_connected_boundary_sides ej ei same
    (fun x hx => ⟨(F ⟨x,hx⟩).1,(F ⟨x,hx⟩).2,front ⟨x,hx⟩⟩) regular)
  obtain ⟨f,e,an,rep⟩ := bounded_one_ended_disk_parameter ow cw (kw.isBounded.subset subset_closure) wt
  obtain ⟨D,interior⟩ := closed_disk_homeomorph_of_circle_limits ow an e rep sides
    (fun _ hz => disk_parameter_circle_limits kw sides an e rep hz)
  exact ⟨D.trans H,fun z => (interior z).trans (values (D z)).2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_planar_patch_closed_disk
