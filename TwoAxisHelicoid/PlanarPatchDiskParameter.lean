import TwoAxisHelicoid.BoundedOneEndedPlaneDisk
import TwoAxisHelicoid.CompactChartPatchBoundary
import TwoAxisHelicoid.RegularBoundaryConnectedTails

namespace TwoAxisHelicoid
open Set Topology Filter Metric Function Bornology Complex
open scoped Topology

/-- A bounded, one-ended open plane domain is parametrized by a
univalent holomorphic function on the disk. The topological inverse
of the extremal coordinate is holomorphic by the local inverse theorem. -/
theorem bounded_one_ended_disk_parameter {W : Set ℂ} (op : IsOpen W) (conn : IsConnected W)
    (bounded : IsBounded W) (tails : HasConnectedCompactTails W) :
    ∃ (f : ℂ → ℂ) (e : complexUnitDisk ≃ₜ W), AnalyticOnNhd ℂ f complexUnitDisk ∧ ∀ x, (e x).1=f x.1 := by
  obtain ⟨p,hp⟩ := conn.nonempty
  obtain ⟨F,h,onto⟩ := bounded_one_ended_plane_disk_coordinate op conn bounded tails hp
  let f := invFunOn F W
  have sur : SurjOn F W complexUnitDisk := onto.symm.subset
  have hol : AnalyticOnNhd ℂ f complexUnitDisk := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := sur hz
    have ax := h.analytic x hx
    have nz := h.regular x hx
    let k := ax.hasStrictDerivAt.localInverse _ _ _ nz
    have ak : AnalyticAt ℂ k (F x) := ax.analyticAt_localInverse nz
    have base : k (F x)=x := (ax.hasStrictDerivAt.eventually_left_inverse nz).self_of_nhds
    apply ak.congr
    filter_upwards [ak.continuousAt.eventually (show W∈𝓝 (k (F x)) by rw [base]; exact op.mem_nhds hx),
      ax.hasStrictDerivAt.eventually_right_inverse nz] with w kw back
    calc k w = f (F (k w)) := (h.injective.leftInvOn_invFunOn kw).symm
         _ = f w := congrArg f back
  let e : complexUnitDisk ≃ₜ W := {
    toFun := fun z => ⟨f z.1,sur.mapsTo_invFunOn z.2⟩
    invFun := fun z => ⟨F z.1,h.maps z.2⟩
    left_inv := fun x => Subtype.ext (sur.rightInvOn_invFunOn x.2)
    right_inv := fun y => Subtype.ext (h.injective.leftInvOn_invFunOn y.2)
    continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp hol.continuousOn).subtype_mk _
    continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp h.analytic.continuousOn).subtype_mk _ }
  exact ⟨f,e,hol,fun _ => rfl⟩

/-- Connected interior sides on the real surface transfer to the planar
model through the original ambient embeddings. This uses the common
open-patch image and the correspondence at its frontier. -/
theorem planar_model_has_connected_boundary_sides {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    {j : ℂ → E} {i : M → E} (ej : IsOpenEmbedding j) (ei : IsOpenEmbedding i)
    {W : Set ℂ} {V : Set M} (same : j '' W=i '' V)
    (front : ∀ x∈frontier W, ∃ y∈frontier V, j x=i y)
    (regular : ∀ y∈frontier V, ∃ e : OpenPartialHomeomorph M (ℝ×ℝ), y∈e.source ∧ e.IsImage V (Iio 0 ×ˢ univ)) :
    ∀ x∈frontier W, ∀ G : Set ℂ, IsOpen G → x∈G →
      ∃ O : Set ℂ, IsOpen O ∧ x∈O ∧ O⊆G ∧ IsPreconnected (O∩W) := by
  intro x hx G og xg
  obtain ⟨y,yv,eq⟩ := front x hx
  obtain ⟨e,ye,side⟩ := regular y yv
  obtain ⟨T,ot,yt,sub,conn⟩ := boundary_half_plane_has_connected_sides e ye side
    ((ej.isOpenMap _ og).preimage ei.continuous) (show y∈i ⁻¹' (j '' G) from ⟨x,xg,eq⟩)
  let O := j ⁻¹' (i '' T)
  have opened : IsOpen O := (ei.isOpenMap _ ot).preimage ej.continuous
  refine ⟨O,opened,⟨y,yt,eq.symm⟩,?_,ej.isInducing.isPreconnected_image.mp ?_⟩
  · rintro w ⟨a,at',wa⟩
    obtain ⟨b,bg,bw⟩ := sub at'
    exact ej.injective (bw.trans wa) ▸ bg
  · have image : j '' (O∩W)=i '' (T∩V) := by
      ext z
      constructor
      · rintro ⟨w,⟨⟨a,at',eq'⟩,ww⟩,rfl⟩
        have av : i a∈i '' V := by rw [← same,eq']; exact mem_image_of_mem _ ww
        exact ⟨a,⟨at',ei.injective.mem_set_image.mp av⟩,eq'⟩
      · rintro ⟨a,⟨at',av⟩,rfl⟩
        obtain ⟨w,ww,wa⟩ := (show i a∈j '' W from same.symm ▸ mem_image_of_mem i av)
        exact ⟨w,⟨⟨a,at',wa.symm⟩,ww⟩,wa⟩
    rw [image]
    exact conn.image _ ei.continuous.continuousOn

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_one_ended_disk_parameter
#print axioms TwoAxisHelicoid.planar_model_has_connected_boundary_sides
