import TwoAxisHelicoid.UnmarkedGenusOneCoreGraph

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- The actual points and signed heights of a complete single sheet in
an open physical tube. The points form an open subset of the moving
surface, and every point of the physical slice is recovered. -/
structure PhysicalCoreGraph {B M E : Type*} [TopologicalSpace B] [TopologicalSpace M]
    (T : B × ℝ → E) (Y : M → E) (r : ℝ) where
  point : B → M
  height : B → ℝ
  open_point : IsOpenEmbedding point
  continuous_height : Continuous height
  inside : ∀ b, |height b|<r
  position : ∀ b, Y (point b)=T (b,height b)
  entire : spatialTubeSlice T (range Y) r=range (fun b => (b,height b))

theorem PhysicalCoreGraph.mem_slice {B M E : Type*} [TopologicalSpace B] [TopologicalSpace M]
    {T : B × ℝ → E} {Y : M → E} {r : ℝ} (G : PhysicalCoreGraph T Y r) (b : B) :
    (b,G.height b)∈spatialTubeSlice T (range Y) r := ⟨G.inside b,G.point b,G.position b⟩

/-- Recover the open marking on the moving surface from the inverse of
the actual foot projection. The inverse is never selected sheetwise. -/
theorem physical_graph_of_homeomorphic_projection {B M E : Type*} [TopologicalSpace B] [TopologicalSpace M]
    [TopologicalSpace E] {T : B × ℝ → E} {Y : M → E} {r : ℝ}
    (tube : IsOpenEmbedding (({q : B × ℝ | |q.2|<r}).domRestrict T)) (embedded : IsEmbedding Y)
    (homeo : IsHomeomorph (fun q : spatialTubeSlice T (range Y) r => q.1.1)) :
    Nonempty (PhysicalCoreGraph T Y r) := by
  obtain ⟨j,oj,space⟩ := physical_tube_slice_open_marking tube embedded
  let e := homeo.isEmbedding.toHomeomorphOfSurjective homeo.surjective
  let h := fun b : B => (e.symm b).1.2
  have pair (b : B) : (b,h b)=(e.symm b).1 := Prod.ext (e.apply_symm_apply b).symm rfl
  refine ⟨⟨j ∘ e.symm,h,oj.comp e.symm.isOpenEmbedding,continuous_snd.comp (continuous_subtype_val.comp e.symm.continuous),
    fun b => (e.symm b).2.1,fun b => (space _).trans (congrArg T (pair b).symm),?_⟩⟩
  ext q
  constructor
  · intro member
    let a : spatialTubeSlice T (range Y) r := ⟨q,member⟩
    exact ⟨q.1,Prod.ext rfl (congrArg (fun u : spatialTubeSlice T (range Y) r => u.1.2) (e.symm_apply_apply a))⟩
  · rintro ⟨b,rfl⟩
    change (b,h b)∈spatialTubeSlice T (range Y) r
    rw [pair]
    exact (e.symm b).2

/-- On a common tail, the complete single sheets have open markings,
uniformly vanishing heights and uniformly convergent unoriented normals.
Every selected normal is already transverse on the whole core. -/
theorem select_transverse_physical_core_graphs {B : Type*} [TopologicalSpace B]
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] {T : B × ℝ → SurfaceEuclideanSpace} {r : ℝ}
    {Y m : ∀ n, M n → SurfaceEuclideanSpace} {N : B → SurfaceEuclideanSpace}
    (tube : IsOpenEmbedding (({q : B × ℝ | |q.2|<r}).domRestrict T)) (embedded : ∀ n, IsEmbedding (Y n))
    (homeo : ∀ᶠ n in atTop, IsHomeomorph (fun q : spatialTubeSlice T (range (Y n)) r => q.1.1))
    (thin : ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ q∈spatialTubeSlice T (range (Y n)) r, |q.2|<ε)
    (normals : ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ q∈spatialTubeSlice T (range (Y n)) r,
      ∀ y, Y n y=T q → coreNormalDistance (m n y) (N q.1)<ε) :
    ∃ k : ℕ, ∃ G : ∀ n, PhysicalCoreGraph T (Y (n+k)) r,
      (∀ n b, coreNormalDistance (m (n+k) ((G n).point b)) (N b)<1) ∧
      ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ b, |(G n).height b|<ε ∧
        coreNormalDistance (m (n+k) ((G n).point b)) (N b)<ε := by
  obtain ⟨k,good⟩ := eventually_atTop.1 (homeo.and (normals 1 zero_lt_one))
  have after (n : ℕ) := good (n+k) (Nat.le_add_left k n)
  let G := fun n => (physical_graph_of_homeomorphic_projection tube (embedded (n+k)) (after n).1).some
  refine ⟨k,G,fun n b => (after n).2 _ ((G n).mem_slice b) _ ((G n).position b),?_⟩
  intro ε ep
  obtain ⟨j,hj⟩ := eventually_atTop.1 ((thin ε ep).and (normals ε ep))
  filter_upwards [eventually_ge_atTop j] with n hn b
  have atn := hj (n+k) (hn.trans (Nat.le_add_right n k))
  exact ⟨atn.1 _ ((G n).mem_slice b),atn.2 _ ((G n).mem_slice b) _ ((G n).position b)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_graph_of_homeomorphic_projection
#print axioms TwoAxisHelicoid.select_transverse_physical_core_graphs
