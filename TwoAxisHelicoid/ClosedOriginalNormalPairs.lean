import TwoAxisHelicoid.RegularOriginalSurfaceNormals

namespace TwoAxisHelicoid
open Set Topology

/-- Over a closed embedded surface, the two graphs of a continuous normal
field form a nonempty closed set of position-normal pairs. -/
theorem closed_normal_pairs {B : Type*} [TopologicalSpace B]
    {X N : B → SurfaceEuclideanSpace} (closed : IsClosedEmbedding X) (cn : Continuous N) (b : B) :
    IsClosed (unorientedSurfaceNormals X N) ∧ (unorientedSurfaceNormals X N).Nonempty := by
  have graph (V : B → SurfaceEuclideanSpace) (cv : Continuous V) : IsClosed (range (fun q => (X q,V q))) := by
    let F := Prod.map X (id : SurfaceEuclideanSpace → SurfaceEuclideanSpace)
    have emb : IsClosedEmbedding F := closed.prodMap (Homeomorph.refl SurfaceEuclideanSpace).isClosedEmbedding
    let G := {q : B × SurfaceEuclideanSpace | q.2=V q.1}
    have gc : IsClosed G := isClosed_eq continuous_snd (cv.comp continuous_fst)
    have image : F '' G=range (fun q => (X q,V q)) := by
      ext v
      constructor
      · rintro ⟨⟨a,w⟩,hw,rfl⟩
        exact ⟨a,Prod.ext rfl hw.symm⟩
      · rintro ⟨a,rfl⟩
        exact ⟨(a,V a),rfl,rfl⟩
    exact image ▸ emb.isClosedMap G gc
  have equal : unorientedSurfaceNormals X N=range (fun q => (X q,N q)) ∪ range (fun q => (X q,-N q)) := by
    ext v
    constructor
    · rintro ⟨q,hx,hv|hv⟩
      · exact Or.inl ⟨q,Prod.ext hx hv.symm⟩
      · exact Or.inr ⟨q,Prod.ext hx hv.symm⟩
    · rintro (⟨q,h⟩|⟨q,h⟩)
      · exact ⟨q,congrArg Prod.fst h,Or.inl (congrArg Prod.snd h).symm⟩
      · exact ⟨q,congrArg Prod.fst h,Or.inr (congrArg Prod.snd h).symm⟩
  refine ⟨?_,⟨(X b,N b),b,rfl,Or.inl rfl⟩⟩
  rw [equal]
  exact (graph N cn).union (graph _ cn.neg)

theorem OriginalSmoothHelicoid.normal_pairs_closed_nonempty (s : OriginalSmoothHelicoid) :
    IsClosed s.unorientedNormals ∧ s.unorientedNormals.Nonempty := by
  obtain ⟨N,cn,_,same,_⟩ := original_smooth_regular_normal_geometry s
  obtain ⟨b,_⟩ := s.axes.vertical 0
  rw [same]
  apply closed_normal_pairs _ cn b
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.closed_normal_pairs
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.normal_pairs_closed_nonempty
