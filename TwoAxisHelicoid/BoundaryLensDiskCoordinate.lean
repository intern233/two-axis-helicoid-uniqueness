import TwoAxisHelicoid.UnivalentSurfaceCoordinate
import TwoAxisHelicoid.HolomorphicSubdomainCoordinate
import Mathlib.Analysis.Convex.Contractible

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function TopologicalSpace
open scoped Topology ContDiff Manifold

/-- A proper simply connected subdomain lying inside one atlas chart
inherits an actual maximal-atlas coordinate onto the unit disk. -/
theorem disk_chart_inside_chart {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (V : Opens M) (sc : IsSimplyConnected (V : Set M)) {a : OpenPartialHomeomorph M ℂ}
    (ah : a∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (src : (V : Set M)⊆a.source)
    {p : M} (ps : p∈a.source) (out : p∉V) :
    ∃ e : OpenPartialHomeomorph M ℂ, e.source=V ∧ e.target=ball 0 1 ∧ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  let S := a '' (V : Set M)
  have op : IsOpen S := a.isOpen_image_of_subset_source V.isOpen src
  let T := a.homeomorphOfImageSubsetSource src (t:=S) rfl
  have non : S.Nonempty := sc.nonempty.image a
  obtain ⟨z,hz⟩ := non
  have proper : S≠univ := fun all => by
    obtain ⟨x,hx,eq⟩ := (show a p∈S from all.symm ▸ mem_univ _)
    exact out ((a.injOn (src hx) ps eq) ▸ hx)
  obtain ⟨f,hf,onto⟩ := simply_connected_plane_riemann_map op (T.toHomotopyEquiv.simplyConnectedSpace_iff.mp sc) proper hz
  let g := fun x : V => f (a x.val)
  have hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g := fun x =>
    (hf.analytic _ (mem_image_of_mem a x.2)).contDiffAt.contMDiffAt.comp x
      ((contMDiffAt_of_mem_maximalAtlas ah (src x.2)).comp x contMDiff_subtype_val.contMDiffAt)
  have inj : Injective g := fun x y eq => Subtype.ext (a.injOn (src x.2) (src y.2)
    (hf.injective (mem_image_of_mem a x.2) (mem_image_of_mem a y.2) eq))
  obtain ⟨W,E,form⟩ := biholomorphic_coordinate_range inj (univalent_surface_local_biholomorphism hol inj)
  obtain ⟨e,es,et,eh⟩ := holomorphic_subdomain_coordinate V W sc.nonempty.to_subtype E
  refine ⟨e,es,et.trans ?_,eh⟩
  change (W : Set ℂ)=complexUnitDisk
  rw [← onto]
  ext y
  constructor
  · intro hy
    let x := E.symm ⟨y,hy⟩
    exact ⟨a x.val,mem_image_of_mem a x.2,(form x).symm.trans (congrArg Subtype.val (E.apply_symm_apply ⟨y,hy⟩))⟩
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    change g ⟨x,hx⟩∈(W : Set ℂ)
    rw [← form]
    exact (E ⟨x,hx⟩).2

/-- A larger disk tangent at a boundary point of the marked round
disk contains every other point of its closure strictly. -/
theorem marked_disk_strict_external_tangency {p z : ℂ} {R : ℝ} (rp : 0<R) (pn : ‖p‖=R)
    (zn : ‖z‖≤R) (ne : z≠p) : dist z (-p)<2*R := by
  have law := parallelogram_law_with_norm ℝ z p
  rw [pn] at law
  rw [dist_eq_norm,sub_neg_eq_add]
  nlinarith [sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ne)),sq_le_sq₀ (norm_nonneg z) rp.le |>.mpr zn,norm_nonneg (z+p)]

/-- For an arbitrary topological marking, every boundary point of a
marked ball has a holomorphic unit-disk chart containing the entire
nearby closed marked ball except for that one point. -/
theorem marked_ball_boundary_lens {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (T : M ≃ₜ ℂ) {R : ℝ} (rp : 0<R) {p : M} (pn : ‖T p‖=R) :
    ∃ (r : ℝ) (e : OpenPartialHomeomorph M ℂ), 0<r ∧
      e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ e.target=ball 0 1 ∧ p∉e.source ∧
      ∀ x, dist (T x) (T p)<r → ‖T x‖≤R → x≠p → x∈e.source := by
  let a := chartAt ℂ p
  have ps : p∈a.source := mem_chart_source ℂ p
  obtain ⟨b,bp,bsub⟩ := Metric.isOpen_iff.mp (T.isOpenMap a.source a.open_source) (T p) (mem_image_of_mem _ ps)
  let L := ball (T p) b ∩ ball (-(T p)) (2*R)
  let V : Opens M := ⟨T ⁻¹' L,(isOpen_ball.inter isOpen_ball).preimage T.continuous⟩
  have out : p∉V := by
    intro hp
    have bad := mem_ball.mp hp.2
    rw [dist_eq_norm,sub_neg_eq_add,← two_smul ℝ (T p),norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),pn] at bad
    exact bad.false
  have sub : (V : Set M)⊆a.source := fun x hx => T.injective.mem_set_image.mp (bsub hx.1)
  have near : T p∈closure (ball (0:ℂ) R) := by rw [closure_ball _ rp.ne',mem_closedBall_zero_iff,pn]
  obtain ⟨z,zb,zd⟩ := Metric.mem_closure_iff.mp near b bp
  have nz : z≠T p := fun eq => (mem_ball_zero_iff.mp zb).not_ge (eq ▸ pn.ge)
  have zl : z∈L := ⟨(show dist z (T p)<b by rwa [dist_comm]),marked_disk_strict_external_tangency rp pn (mem_ball_zero_iff.mp zb).le nz⟩
  let _ : ContractibleSpace L := ((convex_ball (T p) b).inter (convex_ball (-(T p)) (2*R))).contractibleSpace ⟨z,zl⟩
  have sv : IsSimplyConnected (V : Set M) := T.isSimplyConnected_preimage.mpr (inferInstance : SimplyConnectedSpace L)
  obtain ⟨e,es,et,eh⟩ := disk_chart_inside_chart V sv (IsManifold.chart_mem_maximalAtlas p) sub ps out
  refine ⟨b,e,bp,eh,et,es.symm ▸ out,fun x hx size ne => ?_⟩
  rw [es]
  exact ⟨hx,marked_disk_strict_external_tangency rp pn size (T.injective.ne ne)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_ball_boundary_lens
