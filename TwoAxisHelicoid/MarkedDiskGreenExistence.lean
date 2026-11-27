import TwoAxisHelicoid.SurfacePerronPoleData
import TwoAxisHelicoid.MarkedDiskCompactBoundary

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- A boundary subfunction can be raised on the far side of the
compact pole core while its entire singular germ stays fixed. -/
theorem raise_pole_subfunction_at_boundary {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ,ℂ) ω X] {L H B : X → ℝ} (sl : ∀ x, SurfaceSubharmonicAt L x)
    (bounded : L≤H) (sb : ∀ x, SurfaceSubharmonicAt B x) (nb : ∀ x, B x≤0)
    (θ : X → ℝ) (ct : Continuous θ) {s C : ℝ} (sp : 0<s) (cp : 0<C)
    (constant : ∀ x, s≤θ x → B x= -1) (exterior : ∀ x, θ x<2*s → -C≤L x ∧ H x=0) :
    ∃ f : X → ℝ, (∀ x, SurfaceSubharmonicAt f x) ∧ f≤H ∧ ∀ x, θ x<2*s → C*B x≤f x := by
  classical
  let f := fun x => if θ x<2*s then max (L x) (C*B x) else L x
  have outside (x : X) (hx : s≤θ x) : f x=L x := by
    by_cases sm : θ x<2*s
    · rw [show f x=max (L x) (C*B x) from ite_eq_left sm,constant x hx,mul_neg_one,max_eq_left (exterior x sm).1]
    · exact ite_eq_right sm
  refine ⟨f,fun x => ?_,fun x => ?_,fun x sm => (le_max_right _ _).trans_eq (ite_eq_left sm).symm⟩
  · by_cases sm : θ x<2*s
    · have scale : SurfaceSubharmonicAt (fun y => C*B y) x := by simpa only [add_zero] using (sb x).affine_pos cp 0
      apply (surface_subharmonic_max (sl x) scale).congr_germ
      filter_upwards [ct.continuousAt.eventually_lt continuousAt_const sm] with y hy using ite_eq_left hy
    · apply (sl x).congr_germ
      filter_upwards [continuousAt_const.eventually_lt ct.continuousAt (show s<θ x by linarith [le_of_not_gt sm])] with y hy using outside y hy.le
  · by_cases sm : θ x<2*s
    · rw [show f x=max (L x) (C*B x) from ite_eq_left sm]
      exact max_le (bounded x) ((mul_nonpos_of_nonneg_of_nonpos cp.le (nb x)).trans_eq (exterior x sm).2.symm)
    · exact (show f x=L x from ite_eq_right sm).trans_le (bounded x)

/-- Each marked round disk on an arbitrary topological-plane Riemann
surface has a Dirichlet Green function with unit logarithmic coefficient.
The proof constructs the pole functions and forces the boundary values
at every point of the marking circle. -/
theorem marked_disk_dirichlet_green {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (T : M ≃ₜ ℂ) {R : ℝ} (rp : 0<R) :
    ∃ (p : markedBallDomain T R) (ρ : markedBallDomain T R → ℝ), IsDiskGreenModulus p ρ := by
  classical
  let V := markedBallDomain T R
  obtain ⟨patch⟩ := marked_ball_has_quadratic_pole_patch T rp
  obtain ⟨s⟩ := perron_pole_data_of_quadratic_patch patch
  let P := openSurfacePuncture s.p
  have topo := marked_plane_puncture_topology (markedBallPlaneHomeomorph T rp) s.p
  let _ : PreconnectedSpace P := topo.1
  let _ : NoncompactSpace P := topo.2
  obtain ⟨D,ext⟩ := s.exterior
  obtain ⟨K,logBounds⟩ := s.pole_bound
  refine ⟨s.p,green_modulus_from_perron_barriers s.p s.L s.H s.subharmonic s.superharmonic s.order s.nonpositive s.negative logBounds ?_⟩
  intro ε ep
  apply marked_disk_eventually_outside_compact T
  intro q
  let S := (fun x : V => T x.val) '' s.core
  have compact : IsCompact S := s.compact.image (T.continuous.comp continuous_subtype_val)
  have off : q.val∉S := by
    rintro ⟨x,_,eq⟩
    exact (mem_ball.mp x.2).ne ((congrArg (dist · (0:ℂ)) eq).trans (mem_sphere.mp q.2))
  obtain ⟨u,up,avoid⟩ := Metric.mem_nhds_iff.mp (compact.isClosed.isOpen_compl.mem_nhds off)
  let a := u/3
  have ap : 0<a := by dsimp [a]; positivity
  let qM := T.symm q.val
  have tq : T qM=q.val := T.apply_symm_apply _
  have size : ‖T qM‖=R := tq ▸ mem_sphere_zero_iff_norm.mp q.2
  obtain ⟨B,_,_,_,_,_,_,sub,bd,fixed,_,edge⟩ := marked_ball_subharmonic_barrier T rp size ap
  let θ := fun x : P => dist (T x.val.val) q.val
  have clear (x : V) (hx : dist (T x.val) q.val<2*a) : x∉s.core := fun hit =>
    avoid (show T x.val∈ball q.val u by change dist (T x.val) q.val<u; dsimp [a] at hx; linarith) (mem_image_of_mem _ hit)
  let C := max D 1
  have cp : 0<C := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨f,sf,fh,near⟩ := raise_pole_subfunction_at_boundary s.subharmonic s.order
    (fun x : P => surface_subharmonic_open_subtype P x (sub x.val)) (fun x => (bd x.val).2.le) θ
    (((T.continuous.comp continuous_subtype_val).comp continuous_subtype_val).dist continuous_const) ap cp
    (fun x hx => fixed x.val (by rwa [tq])) (fun x hx =>
      ⟨(neg_le_neg (le_max_left _ _)).trans (ext x (clear x.val hx)).1,(ext x (clear x.val hx)).2⟩)
  obtain ⟨b,bp,Bgood⟩ := edge (ε/C) (div_pos ep cp)
  refine ⟨min b a,lt_min bp ap,fun x hx => ?_⟩
  have lt := hx.trans_le (min_le_right _ _)
  have inner : dist (T x.val) q.val<2*a := by linarith
  have np : x≠s.p := fun eq => clear x inner (eq ▸ s.pole_mem)
  let w : P := ⟨x,np⟩
  refine ⟨f,sf,fh,?_⟩
  change -ε<openSetExtension P f x
  rw [show openSetExtension P f x=f w from openSetExtension_val P f w]
  have positive := Bgood x (by rw [tq]; exact hx.trans_le (min_le_left _ _))
  have h : -ε<C*B x := by
    have eq : C*(-(ε/C))= -ε := by field_simp
    linarith [mul_lt_mul_of_pos_left positive cp]
  exact h.trans_le (near w inner)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_disk_dirichlet_green
