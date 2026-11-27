import TwoAxisHelicoid.PlanarChartComplement
import TwoAxisHelicoid.BallComponentComplement
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology OnePoint Manifold

/-- A compact surface has an actual open plane coordinate at every
point, with nonempty complement. -/
theorem compact_surface_open_plane_at {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P] [CompactSpace P] (p : P) :
    ∃ j : ℂ → P, IsOpenEmbedding j ∧ j 0=p ∧ ∃ y, y∉range j := by
  let e := chartAt ℂ p
  have hp : p∈e.source := mem_chart_source _ _
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hp))
  let a := OpenPartialHomeomorph.univBall (e p) r
  let k := a.trans e.symm
  have all : k.source=univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x∈a.source := by simp [a]
    refine ⟨hx,sub ?_⟩
    change a x∈ball (e p) r
    simpa only [a,OpenPartialHomeomorph.univBall_target _ rp] using a.map_source hx
  have emb := k.isOpenEmbedding all
  refine ⟨k,emb,by change e.symm (a 0)=p; rw [show a 0=e p from OpenPartialHomeomorph.univBall_apply_zero _ _,e.left_inv hp],?_⟩
  by_contra! full
  have K : IsCompact (k '' (univ : Set ℂ)) := by rw [image_univ,eq_univ_of_forall full]; exact isCompact_univ
  exact noncompact_univ ℂ (emb.isEmbedding.isCompact_iff.mpr K)

/-- A fixed disk chart at the added end contains every sufficiently
distant closed extrinsic ball preimage. Each connected open component
is represented by a relatively compact plane domain with preconnected
spherical complement; the statement allows critical radii. -/
theorem proper_far_ball_components_in_plane {M E : Type*} [TopologicalSpace M] [T2Space M] [LocallyConnectedSpace M]
    [NoncompactSpace M] [LocallyCompactSpace M] [NormedAddCommGroup E] [ProperSpace E] (X : M → E) (proper : IsProperMap X)
    {j : ℂ → OnePoint M} (emb : IsOpenEmbedding j) (inf : ∞∈range j) (extra : ∃ y, y∉range j)
    (exterior : ∀ c r p, IsPreconnected (connectedComponentIn (X ⁻¹' ball c r) p)ᶜ) (r : ℝ) :
    ∃ B : ℝ, ∀ c : E, B≤‖c‖ → ∀ p : M, p∈X ⁻¹' ball c r →
      ∃ W : Set ℂ, IsOpen W ∧ IsConnected W ∧ IsCompact (closure W) ∧
        IsPreconnected ((OnePoint.some : ℂ → OnePoint ℂ) '' W)ᶜ ∧
        j '' W=(OnePoint.some : M → OnePoint M) '' connectedComponentIn (X ⁻¹' ball c r) p := by
  have K := ((OnePoint.isOpen_iff_of_mem' inf).mp emb.isOpen_range).1
  obtain ⟨T,size⟩ := (K.image proper.continuous).isBounded.exists_norm_le
  refine ⟨T+r+1,?_⟩
  intro c far p inside
  let A := X ⁻¹' closedBall c r
  have comp : IsCompact A := proper.isCompact_preimage (isCompact_closedBall _ _)
  have sub : (OnePoint.some : M → OnePoint M) '' A⊆range j := by
    rintro _ ⟨x,hx,rfl⟩
    by_contra nx
    have n := size (X x) (mem_image_of_mem X nx)
    have d := norm_sub_norm_le c (X x)
    rw [← dist_eq_norm,dist_comm] at d
    have h : dist (X x) c≤r := hx
    linarith
  let V := connectedComponentIn (X ⁻¹' ball c r) p
  have vs : V⊆A := (connectedComponentIn_subset _ _).trans (preimage_mono ball_subset_closedBall)
  have vk := comp.of_isClosed_subset isClosed_closure (closure_minimal vs comp.isClosed)
  let Q := (OnePoint.some : M → OnePoint M) '' V
  let W := j ⁻¹' Q
  have qj : Q⊆range j := (image_mono vs).trans sub
  have eq : j '' W=Q := image_preimage_eq_of_subset qj
  have vo : IsOpen V := (isOpen_ball.preimage proper.continuous).connectedComponentIn
  have vc : IsConnected V := ⟨⟨p,mem_connectedComponentIn inside⟩,isPreconnected_connectedComponentIn⟩
  have fit : W ⊆ j ⁻¹' ((OnePoint.some : M → OnePoint M) '' A) := preimage_mono (image_mono vs)
  have bounded := emb.isEmbedding.isInducing.isCompact_preimage' (comp.image OnePoint.continuous_coe) sub
  refine ⟨W,((OnePoint.isOpen_image_coe).mpr vo).preimage emb.continuous,
    (vc.image _ OnePoint.continuous_coe.continuousOn).preimage_of_isOpenMap emb.injective emb.isOpenMap qj,
    bounded.of_isClosed_subset isClosed_closure (closure_minimal fit bounded.isClosed),?_,eq⟩
  exact chart_spherical_complement_preconnected emb qj (one_point_complement_of_relatively_compact vk (exterior c r p)) extra

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_surface_open_plane_at
#print axioms TwoAxisHelicoid.proper_far_ball_components_in_plane
