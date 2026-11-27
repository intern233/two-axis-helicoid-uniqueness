import TwoAxisHelicoid.OriginalUnmarkedCoreC1

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A unit normal of the given reference immersion in its real surface charts. -/
def RegularSurfaceNormalInCharts {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    (X N : B → SurfaceEuclideanSpace) : Prop :=
  Continuous N ∧ ∀ p, let e := chartAt ℂ p; let z := e p
    ContDiffAt ℝ 1 (X ∘ e.symm) z ∧ ContDiffAt ℝ 1 (N ∘ e.symm) z ∧
    Function.Injective (fderiv ℝ (X ∘ e.symm) z) ∧ ‖N p‖=1 ∧ ∀ v, ⟪fderiv ℝ (X ∘ e.symm) z v,N p⟫=0

/-- Over any compactly carried open handle, local convergence of positions
and unoriented normals gives open copies on every sufficiently late moving
torus. Their positions are uniformly close to the given parametrization of
the handle. The rest of the reference surface may have arbitrary topology. -/
theorem local_normal_limit_transports_open_handle {B : Type*} [TopologicalSpace B] [T2Space B]
    [ChartedSpace ℂ B] (X N : B → SurfaceEuclideanSpace) (closed : IsClosedEmbedding X)
    (normal : RegularSurfaceNormalInCharts X N) (moving : ℕ → OriginalSmoothHelicoid)
    (conv : LocalSpatialImageLimit (fun n => (moving n).unorientedNormals) (unorientedSurfaceNormals X N))
    {A : PeriodPair} (C : TorusGeneratingCoreModel A) (f : C.carrier → B) (op : IsOpenEmbedding f)
    (K : Set B) (compact : IsCompact K) (inside : range f⊆K) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∃ j : C.carrier → (moving n).carrier, IsOpenEmbedding j ∧
      ∀ b, ‖(moving n).euclideanPosition (j b)-X (f b)‖<ε := by
  let V := range f
  let e : C.carrier ≃ₜ V := op.isEmbedding.toHomeomorph
  have kc : IsCompact (closure V) := compact.of_isClosed_subset isClosed_closure (closure_minimal inside compact.isClosed)
  obtain ⟨U,r,uo,ku,rp,tube⟩ := compact_immersed_core_normal_tube kc closed.injective.injOn (fun y _ => normal.2 y)
  choose field _ units norms charts regular using (fun n => original_smooth_regular_normal_geometry (moving n))
  have chart (n : ℕ) (y : (moving n).carrier) : ∃ a : OpenPartialHomeomorph (moving n).carrier ℂ, y∈a.source ∧
      ContDiffAt ℝ 1 ((moving n).euclideanPosition ∘ a.symm) (a y) ∧
      Function.Injective (fderiv ℝ ((moving n).euclideanPosition ∘ a.symm) (a y)) ∧
      ∀ v, ⟪fderiv ℝ ((moving n).euclideanPosition ∘ a.symm) (a y) v,field n y⟫=0 :=
    ⟨(charts n).chartAt y,(charts n).mem_chart_source y,(regular n y).1,(regular n y).2.2.1,(regular n y).2.2.2.2⟩
  have embedded (s : OriginalSmoothHelicoid) : IsClosedEmbedding s.euclideanPosition :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding
  have limit : LocalSpatialImageLimit (fun n => unorientedSurfaceNormals (moving n).euclideanPosition (field n))
      (unorientedSurfaceNormals X N) := by simpa only [norms] using conv
  obtain ⟨R,_,_,k,G,_,near⟩ := unmarked_handles_select_transverse_core_graphs C closed normal.1
    op.isOpen_range e.symm kc (fun y _ => ⟨chartAt ℂ y,mem_chart_source ℂ y,normal.2 y⟩)
    uo ku rp tube (fun n => (moving n).topologicalType) (fun n => (moving n).euclideanPosition)
    field (fun n => embedded (moving n)) units chart limit
  intro ε ep
  obtain ⟨l,late⟩ := eventually_atTop.mp (near ε ep)
  filter_upwards [eventually_ge_atTop (l+k)] with n hn
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le' ((Nat.le_add_left k l).trans hn)
  have hi : l ≤ i := by omega
  refine ⟨(G i).point ∘ e,(G i).open_point.comp e.isOpenEmbedding,?_⟩
  intro b
  change ‖(moving (i+k)).euclideanPosition ((G i).point (e b))-X (e b).1‖<ε
  rw [(G i).position]
  change ‖X (e b).1+(G i).height (e b) • N (e b).1-X (e b).1‖<ε
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,(normal.2 (e b).1).2.2.2.1,mul_one]
  exact (late i hi (e b)).1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.local_normal_limit_transports_open_handle
