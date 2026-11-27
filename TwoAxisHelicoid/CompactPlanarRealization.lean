import TwoAxisHelicoid.ExhaustingChartBounds

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology
open scoped Topology ContDiff Manifold

universe u

/-- Only relatively compact pieces need a planar coordinate. The
functions on different compact sets have no prescribed compatibility. -/
def HasPlanarCoordinatesOnCompacts (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M] : Prop :=
  ∀ K : Set M, IsCompact K → ∃ (V : Set M) (f : M → ℂ), IsOpen V ∧ K⊆V ∧
    ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f V ∧ InjOn f V

/-- A univalent chart can be normalized by an affine transformation
of its range using the first jet in any prescribed source chart. -/
theorem normalize_univalent_surface_chart {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {V : Set M} (op : IsOpen V) {f : M → ℂ}
    (hol : ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f V) (inj : InjOn f V) {p : M} (hp : p∈V) :
    ∃ F : M → ℂ, ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F V ∧ InjOn F V ∧ F p=0 ∧
      deriv (F ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)=1 := by
  let e := chartAt ℂ p
  have ps : p∈e.source := mem_chart_source ℂ p
  let S := e.target ∩ e.symm ⁻¹' V
  have so : IsOpen S := e.symm.continuousOn.isOpen_inter_preimage e.open_target op
  have pc : e p∈S := ⟨e.map_source ps,by simpa only [mem_preimage,e.left_inv ps] using hp⟩
  let g := f ∘ e.symm
  have an : AnalyticOnNhd ℂ g S := fun z hz =>
    ((hol.contMDiffAt (op.mem_nhds hz.2)).comp z (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) p) hz.1)).contDiffAt.analyticAt
  have injg : InjOn g S := inj.comp (e.symm.injOn.mono inter_subset_left) (fun z hz => hz.2)
  let D := deriv g (e p)
  have nz : D≠0 := univalent_analytic_deriv_ne_zero so an injg pc
  let F := fun x => (f x-f p)/D
  have affine : ContDiff ℂ ω (fun z : ℂ => (z-f p)/D) :=
    (contDiff_id.sub contDiff_const).div_const _
  refine ⟨F,affine.contMDiff.comp_contMDiffOn hol,fun x hx y hy eq => ?_,by simp [F],?_⟩
  · exact inj hx hy (sub_left_inj.mp ((div_left_inj' nz).mp eq))
  · have h := ((an _ pc).differentiableAt.hasDerivAt.sub_const (f p)).div_const D
    change HasDerivAt (F ∘ e.symm) (D/D) (e p) at h
    simpa [nz] using h.deriv

/-- Uniformization of an abstract topological plane reduces to
realizing each compact subset in some plane domain. The global chart
is obtained by a common limit of affine-normalized local coordinates. -/
theorem topological_plane_univalent_of_compact_coordinates {M : Type u} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] (T : M ≃ₜ ℂ) (localCoordinates : HasPlanarCoordinatesOnCompacts M) :
    ∃ F : M → ℂ, Injective F ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F := by
  classical
  let _ : T2Space M := T.isEmbedding.t2Space
  let _ : ContractibleSpace M := T.contractibleSpace
  let p := T.symm 0
  let K := fun n : ℕ => T.symm '' closedBall (0:ℂ) ((n:ℝ)+1)
  have comp (n : ℕ) : IsCompact (K n) := (isCompact_closedBall _ _).image T.symm.continuous
  choose U f op sub hol inj using fun n => localCoordinates (K n) (comp n)
  have inside (n : ℕ) : p∈U n := sub n (mem_image_of_mem _ (mem_closedBall_self (by positivity)))
  choose F an inject jet using fun n => normalize_univalent_surface_chart (op n) (hol n) (inj n) (inside n)
  let l := Ultrafilter.of (atTop : Filter ℕ)
  have ex (A : Set M) (ck : IsCompact A) : ∀ᶠ n in (l : Filter ℕ), A⊆U n := by
    obtain ⟨r,ar⟩ := (isBounded_iff_subset_closedBall (0:ℂ)).mp (ck.image T.continuous).isBounded
    obtain ⟨N,hN⟩ := exists_nat_gt r
    filter_upwards [(eventually_ge_atTop N).filter_mono (Ultrafilter.of_le (atTop : Filter ℕ))] with n hn
    intro x hx
    apply sub n
    refine ⟨T x,?_,T.symm_apply_apply x⟩
    apply closedBall_subset_closedBall _ (ar (mem_image_of_mem _ hx))
    have : (N:ℝ)≤n := Nat.cast_le.mpr hn
    linarith
  have normalized : ∀ᶠ n in (l : Filter ℕ), F n p=0 ∧ deriv (F n ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)=1 :=
    .of_forall jet
  exact surface_coordinate_of_bounded_exhaustion l U F op an inject
    (normalized_univalent_exhaustion_bounded op an inject ex p normalized) p (normalized.mono fun _ h => h.2)

/-- There is no global assumption on the charts in this sufficient
condition for the classification of all annular ends. -/
theorem annular_uniformization_of_compact_coordinates
    (compactCoordinates : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M]
      [IsManifold 𝓘(ℂ,ℂ) ω M], Nonempty (M ≃ₜ ℂ) → HasPlanarCoordinatesOnCompacts M) :
    AnnularRiemannSurfaceUniformization.{u} := by
  apply annular_classification_of_plane_uniformization
  apply plane_uniformization_of_univalent_function
  intro M _ _ _ home
  exact topological_plane_univalent_of_compact_coordinates home.some (compactCoordinates M home)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.topological_plane_univalent_of_compact_coordinates
#print axioms TwoAxisHelicoid.annular_uniformization_of_compact_coordinates
