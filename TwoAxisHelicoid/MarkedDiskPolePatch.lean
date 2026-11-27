import TwoAxisHelicoid.MarkedDiskBoundaryBarrier
import TwoAxisHelicoid.OpenSubdomainLocalBiholomorphism
import TwoAxisHelicoid.CappedSurfaceChartRadius

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- Restriction of a maximal-atlas coordinate to an open submanifold,
with its values, holomorphic inverse and source recorded. -/
theorem restrict_maximal_surface_chart {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (V : Opens M) [Nonempty V] {e : OpenPartialHomeomorph M ℂ}
    (eh : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    ∃ a : OpenPartialHomeomorph V ℂ, a∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω V ∧
      (∀ x : V, a x=e x.val) ∧ ∀ x : V, x∈a.source ↔ x.val∈e.source := by
  let i := V.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : V → M)
  have inv : ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω i.symm i.target := by
    intro z hz
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff i.symm i.target z).mp
    exact contMDiffWithinAt_id.congr (fun w hw => i.right_inv hw) (i.right_inv hz)
  refine ⟨i.trans e,(i.trans e).mem_maximalAtlas_of_contMDiffOn ?_ ?_,fun x => rfl,fun x => ⟨fun h => h.2,fun h => ⟨mem_univ _,h⟩⟩⟩
  · intro x hx
    exact ((contMDiffAt_of_mem_maximalAtlas eh hx.2).comp x contMDiff_subtype_val.contMDiffAt).contMDiffWithinAt
  · intro z hz
    exact ((inv.contMDiffAt (i.open_target.mem_nhds hz.2)).comp z (contMDiffAt_symm_of_mem_maximalAtlas eh hz.1)).contMDiffWithinAt

/-- A bounded global subfunction with a genuine quadratic piece on
a closed coordinate disk. This data suffices for logarithmic insertion. -/
structure QuadraticSurfacePolePatch (N : Type*) [TopologicalSpace N] [ChartedSpace ℂ N] where
  p : N
  chart : OpenPartialHomeomorph N ℂ
  maximal : chart∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N
  in_source : p∈chart.source
  r : ℝ
  positive : 0<r
  domain : closedBall (chart p) (2*r)⊆chart.target
  B : N → ℝ
  subharmonic : ∀ x, SurfaceSubharmonicAt B x
  bounded : ∀ x, -1≤B x ∧ B x≤0
  A : ℝ
  weight : 0<A
  quadratic : ∀ x∈chart.source, ‖chart x-chart p‖<2*r → B x=A*(‖chart x‖^2-1)

/-- The boundary barrier is active at some interior point; after
restricting the actual holomorphic chart its untruncated quadratic
formula holds throughout an honest closed neighborhood of that point. -/
theorem marked_ball_has_quadratic_pole_patch {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (T : M ≃ₜ ℂ) {R : ℝ} (rp : 0<R) :
    Nonempty (QuadraticSurfacePolePatch (markedBallDomain T R)) := by
  let V := markedBallDomain T R
  let q := T.symm (R:ℂ)
  have normq : ‖T q‖=R := by rw [show T q=(R:ℂ) from T.apply_symm_apply _,Complex.norm_real,Real.norm_of_nonneg rp.le]
  obtain ⟨B,e,A,b,ap,bp,eh,sb,bd,_,form,edge⟩ := marked_ball_subharmonic_barrier T rp normq (s:=1) zero_lt_one
  obtain ⟨d,dp,near⟩ := edge 1 zero_lt_one
  have cl : T q∈closure (ball (0:ℂ) R) := by rw [closure_ball _ rp.ne',mem_closedBall_zero_iff,normq]
  obtain ⟨z,hz,distz⟩ := Metric.mem_closure_iff.mp cl (min d b) (lt_min dp bp)
  let p : V := ⟨T.symm z,by change T (T.symm z)∈ball 0 R; rwa [T.apply_symm_apply]⟩
  have sz : dist (T p.val) (T q)<min d b := by change dist (T (T.symm z)) (T q)<_; rw [T.apply_symm_apply,dist_comm]; exact distz
  have pb := sz.trans_le (min_le_right _ _)
  have active := near p (sz.trans_le (min_le_left _ _))
  let _ : Nonempty V := ⟨p⟩
  obtain ⟨a,ah,av,src⟩ := restrict_maximal_surface_chart V eh
  have ps := (src p).mpr (form p pb).1
  let W := {x : V | -1<B x ∧ dist (T x.val) (T q)<b}
  have cw : Continuous B := continuous_iff_continuousAt.mpr fun x => (sb x).1
  have wo : IsOpen W := (isOpen_lt continuous_const cw).inter (isOpen_lt ((T.continuous.comp continuous_subtype_val).dist continuous_const) continuous_const)
  let U := a.target∩a.symm ⁻¹' W
  have uo : IsOpen U := a.symm.continuousOn.isOpen_inter_preimage a.open_target wo
  have ua : a p∈U := ⟨a.map_source ps,by change a.symm (a p)∈W; rw [a.left_inv ps]; exact ⟨active,pb⟩⟩
  obtain ⟨s,sp,sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (uo.mem_nhds ua)
  let r := s/2
  have radius : 2*r=s := by dsimp [r]; ring
  refine ⟨⟨p,a,ah,ps,r,half_pos sp,?_,B,sb,fun x => ⟨(bd x).1,(bd x).2.le⟩,A,ap,?_⟩⟩
  · rw [radius]; exact sub.trans inter_subset_left
  · intro x xs dx
    rw [radius] at dx
    obtain ⟨_,hw⟩ := sub (show a x∈closedBall (a p) s from mem_closedBall.mpr (by rw [dist_eq_norm]; exact dx.le))
    have wx : x∈W := by change a.symm (a x)∈W at hw; rwa [a.left_inv xs] at hw
    have m := (form x wx.2).2
    have lt : -1<A*(‖e x.val‖^2-1) := (lt_max_iff.mp (wx.1.trans_eq m)).resolve_left (lt_irrefl _)
    rw [av,m,max_eq_right lt.le]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_ball_has_quadratic_pole_patch
