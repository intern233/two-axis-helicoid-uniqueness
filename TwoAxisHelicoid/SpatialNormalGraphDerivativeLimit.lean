import TwoAxisHelicoid.TransversePhysicalGraphRegularity
import TwoAxisHelicoid.TransverseCoreTubeSheets

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- In a transverse physical normal graph the moving point in its own
chart, the signed height and the true spatial position are smooth to the
order of the parametrizations. Orthogonality is preserved by transport. -/
theorem transverse_graph_regular_in_moving_chart {M : Type*} [TopologicalSpace M]
    {X N : ℂ → SurfaceEuclideanSpace} {Y : M → SurfaceEuclideanSpace} {u : ℂ → ℝ} {f : ℂ → M}
    (a : OpenPartialHomeomorph M ℂ) {z : ℂ} {n : ℕ∞ω} (nz : n≠0) (inside : f z∈a.source)
    (sx : ContDiffAt ℝ n X z) (sn : ContDiffAt ℝ n N z) (sy : ContDiffAt ℝ n (Y ∘ a.symm) (a (f z)))
    (inj : Function.Injective (fderiv ℝ (Y ∘ a.symm) (a (f z)))) {m : SurfaceEuclideanSpace}
    (perp : ∀ v, ⟪fderiv ℝ (Y ∘ a.symm) (a (f z)) v,m⟫=0) (unit : ‖m‖=1)
    (near : coreNormalDistance m (N z)<1) (cu : ContinuousAt u z) (cf : ContinuousAt f z)
    (graph : (Y ∘ f) =ᶠ[𝓝 z] (fun w => X w+u w • N w)) :
    ContDiffAt ℝ n (a ∘ f) z ∧ ContDiffAt ℝ n u z ∧ ContDiffAt ℝ n (Y ∘ f) z ∧
      ∀ v, ⟪fderiv ℝ (Y ∘ f) z v,m⟫=0 := by
  have germ : (Y ∘ a.symm) ∘ (a ∘ f) =ᶠ[𝓝 z] Y ∘ f := by
    filter_upwards [cf.preimage_mem_nhds (a.open_source.mem_nhds inside)] with w hw
    exact congrArg Y (a.left_inv hw)
  have angle : ⟪N z,m⟫≠0 := nearby_core_normals_transverse unit (by
    simpa only [coreNormalDistance,norm_sub_rev (N z) m,add_comm (N z) m,min_lt_iff] using near)
  obtain ⟨mark,height,spatial,ort⟩ := continuous_transverse_normal_graph_regular (g := a ∘ f)
    nz sx sn sy inj perp angle cu ((a.continuousAt inside).comp cf) (germ.trans graph)
  refine ⟨mark,height,spatial.congr_of_eventuallyEq germ.symm,?_⟩
  intro v
  rw [← germ.fderiv_eq (𝕜 := ℝ)]
  exact ort v

/-- On an open parameter region, unmarked plane estimates and small
normal heights imply C¹ convergence of the actual spatial maps.
The graph heights and moving point maps need only be continuous.
The moving chart may be chosen separately at every point. -/
theorem continuous_spatial_normal_graphs_converge_C1 {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    {U : Set ℂ} (op : IsOpen U) (X N : ℂ → SurfaceEuclideanSpace) (Y : ∀ k, M k → SurfaceEuclideanSpace)
    (f : ∀ k, ℂ → M k) (u : ℕ → ℂ → ℝ) (m : ℕ → ℂ → SurfaceEuclideanSpace)
    (sx : ∀ z∈U, ContDiffAt ℝ 1 X z) (sn : ∀ z∈U, ContDiffAt ℝ 1 N z)
    (ref : ∀ z∈U, ‖N z‖=1 ∧ ∀ v, ⟪fderiv ℝ X z v,N z⟫=0)
    (cf : ∀ k, ContinuousOn (f k) U) (cu : ∀ k, ContinuousOn (u k) U)
    (graph : ∀ k z, z∈U → Y k (f k z)=X z+u k z • N z)
    (regular : ∀ k z, z∈U → ∃ a : OpenPartialHomeomorph (M k) ℂ, f k z∈a.source ∧
      ContDiffAt ℝ 1 (Y k ∘ a.symm) (a (f k z)) ∧ Function.Injective (fderiv ℝ (Y k ∘ a.symm) (a (f k z))) ∧
      ∀ v, ⟪fderiv ℝ (Y k ∘ a.symm) (a (f k z)) v,m k z⟫=0)
    (unit : ∀ k z, z∈U → ‖m k z‖=1) (near : ∀ k z, z∈U → coreNormalDistance (m k z) (N z)<1)
    (heights : TendstoLocallyUniformlyOn u (fun _ => 0) atTop U)
    (planes : TendstoLocallyUniformlyOn (fun k z => coreNormalDistance (m k z) (N z)) (fun _ => 0) atTop U) :
    (∀ k z, z∈U → ContDiffAt ℝ 1 (u k) z ∧ ContDiffAt ℝ 1 (Y k ∘ f k) z) ∧
    TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) (fun _ => 0) atTop U ∧
    TendstoLocallyUniformlyOn (fun k => fderiv ℝ (Y k ∘ f k)) (fderiv ℝ X) atTop U := by
  have smooth (k : ℕ) (z : ℂ) (hz : z∈U) : ContDiffAt ℝ 1 (u k) z ∧ ContDiffAt ℝ 1 (Y k ∘ f k) z ∧
      ∀ v, ⟪fderiv ℝ (Y k ∘ f k) z v,m k z⟫=0 := by
    obtain ⟨a,az,sy,inj,orth⟩ := regular k z hz
    exact (transverse_graph_regular_in_moving_chart a one_ne_zero az (sx z hz) (sn z hz) sy inj orth
      (unit k z hz) (near k z hz) ((cu k z hz).continuousAt (op.mem_nhds hz)) ((cf k z hz).continuousAt (op.mem_nhds hz))
      (Filter.mem_of_superset (op.mem_nhds hz) (fun w hw => graph k w hw))).2
  refine ⟨fun k z hz => ⟨(smooth k z hz).1,(smooth k z hz).2.1⟩,?_⟩
  apply physical_plane_convergence_gives_core_derivative_convergence op X N (fun k => Y k ∘ f k) m u sx sn
    (fun k z hz => (smooth k z hz).1.differentiableAt one_ne_zero) graph _ _ heights planes
  · intro z hz
    exact ⟨(ref z hz).1,fun v => (real_inner_comm _ _).trans ((ref z hz).2 v)⟩
  · intro k z hz
    exact ⟨unit k z hz,fun v => (real_inner_comm _ _).trans ((smooth k z hz).2.2 v)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.transverse_graph_regular_in_moving_chart
#print axioms TwoAxisHelicoid.continuous_spatial_normal_graphs_converge_C1
