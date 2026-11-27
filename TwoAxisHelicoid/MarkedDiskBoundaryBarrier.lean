import TwoAxisHelicoid.BoundaryLensDiskCoordinate
import TwoAxisHelicoid.HolomorphicBoundaryBarrier

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- The norm of a unit-disk chart tends to one at every omitted
boundary point, by compactness of every smaller closed coordinate disk. -/
theorem disk_chart_boundary_norm {M : Type*} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph M ℂ) (target : e.target=ball 0 1) {p : M} (off : p∉e.source) :
    Tendsto (fun x => ‖e x‖) (𝓝[e.source] p) (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let K := e.symm '' closedBall 0 (1-ε)
  have sub : closedBall (0:ℂ) (1-ε)⊆e.target := target.symm ▸ closedBall_subset_ball (by linarith)
  have ck : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono sub)
  have pk : p∉K := by rintro ⟨z,hz,rfl⟩; exact off (e.map_target (sub hz))
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ck.isClosed.isOpen_compl.mem_nhds pk)] with x xs outside
  have unit : ‖e x‖<1 := mem_ball_zero_iff.mp (target ▸ e.map_source xs)
  have low : 1-ε<‖e x‖ := lt_of_not_ge fun le => outside ⟨e x,mem_closedBall_zero_iff.mpr le,e.left_inv xs⟩
  rw [Real.dist_eq,abs_of_neg (sub_neg.mpr unit)]
  linarith

def markedBallDomain {M : Type*} [TopologicalSpace M] (T : M ≃ₜ ℂ) (R : ℝ) : Opens M :=
  ⟨T ⁻¹' ball 0 R,isOpen_ball.preimage T.continuous⟩

/-- Every point of the boundary of a topologically marked disk admits
a continuous negative subharmonic barrier, constant outside an arbitrarily
small neighborhood. Its explicit inner formula is strictly subharmonic
where the truncation is inactive. -/
theorem marked_ball_subharmonic_barrier {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (T : M ≃ₜ ℂ) {R : ℝ} (rp : 0<R) {p : M} (pn : ‖T p‖=R)
    {s : ℝ} (sp : 0<s) : let V := markedBallDomain T R
    ∃ (B : V → ℝ) (e : OpenPartialHomeomorph M ℂ) (A b : ℝ), 0<A ∧ 0<b ∧
      e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ (∀ x, SurfaceSubharmonicAt B x) ∧
      (∀ x, -1≤B x ∧ B x<0) ∧ (∀ x : V, s≤dist (T x.val) (T p) → B x= -1) ∧
      (∀ x : V, dist (T x.val) (T p)<b → x.val∈e.source ∧ B x=max (-1) (A*(‖e x.val‖^2-1))) ∧
      ∀ ε>0, ∃ d>0, ∀ x : V, dist (T x.val) (T p)<d → -ε<B x := by
  classical
  let V := markedBallDomain T R
  obtain ⟨r,e,rp',eh,et,off,covers⟩ := marked_ball_boundary_lens T rp pn
  let b := min r s / 2
  let a := b/2
  have bp : 0<b := half_pos (lt_min rp' sp)
  have ap : 0<a := half_pos bp
  have br : b<r := (half_lt_self (lt_min rp' sp)).trans_le (min_le_left _ _)
  have bs : b<s := (half_lt_self (lt_min rp' sp)).trans_le (min_le_right _ _)
  have ab : a<b := half_lt_self bp
  let θ := fun x : V => dist (T x.val) (T p)
  have ct : Continuous θ := (T.continuous.comp continuous_subtype_val).dist continuous_const
  have coord (x : V) (hx : θ x<b) : x.val∈e.source := by
    have size : ‖T x.val‖<R := mem_ball_zero_iff.mp x.2
    exact covers x.val (hx.trans br) size.le (fun eq => size.ne (eq ▸ pn))
  let K := T.symm '' ((closedBall (T p) b \ ball (T p) a) ∩ closedBall 0 R)
  have ck : IsCompact K := (((isCompact_closedBall _ _).diff isOpen_ball).inter_right isClosed_closedBall).image T.symm.continuous
  have src : K⊆e.source := by
    rintro _ ⟨z,⟨⟨hzb,hza⟩,hzR⟩,rfl⟩
    apply covers
    · simpa only [T.apply_symm_apply] using (mem_closedBall.mp hzb).trans_lt br
    · simpa only [T.apply_symm_apply] using mem_closedBall_zero_iff.mp hzR
    · intro eq
      have h := (T.apply_symm_apply z).symm.trans (congrArg T eq)
      exact hza (h.symm ▸ mem_ball_self ap)
  have bound : ∃ k<1, ∀ x∈K, ‖e x‖^2≤k := by
    rcases K.eq_empty_or_nonempty with none|some
    · exact ⟨0,zero_lt_one,fun x hx => (notMem_empty x (none ▸ hx)).elim⟩
    obtain ⟨w,hw,mx⟩ := ck.exists_isMaxOn some ((e.continuousOn.mono src).norm.pow 2)
    have less := mem_ball_zero_iff.mp (et ▸ e.map_source (src hw))
    exact ⟨_,by simpa using (sq_lt_sq₀ (norm_nonneg (e w)) zero_le_one).mpr less,fun _ hx => mx hx⟩
  obtain ⟨k,k1,ks⟩ := bound
  obtain ⟨B,A,Apos,sub,Bbd,ext,formula⟩ := truncated_coordinate_boundary_barrier θ ct ab k1
    (fun x : V => e x.val) (fun x hx => (contMDiffAt_of_mem_maximalAtlas eh (coord x hx)).comp x contMDiff_subtype_val.contMDiffAt)
    (fun x hx => mem_ball_zero_iff.mp (et ▸ e.map_source (coord x hx))) (fun x lo hi =>
      ks x.val ⟨T x.val,⟨⟨hi.le,not_lt.mpr lo⟩,ball_subset_closedBall x.2⟩,T.symm_apply_apply _⟩)
  refine ⟨B,e,A,b,Apos,bp,eh,sub,Bbd,fun x h => ext x (ab.le.trans (bs.le.trans h)),
    fun x hx => ⟨coord x hx,formula x hx⟩,?_⟩
  intro ε ep
  have normlim := disk_chart_boundary_norm e et off
  have lim : Tendsto (fun x => A*(‖e x‖^2-1)) (𝓝[e.source] p) (𝓝 (A*(1^2-1))) :=
    tendsto_const_nhds.mul ((normlim.pow 2).sub_const 1)
  have near := eventually_nhdsWithin_iff.mp (lim.eventually (lt_mem_nhds (show -ε<A*(1^2-1) by linarith)))
  have back : Tendsto T.symm (𝓝 (T p)) (𝓝 p) := by simpa only [T.symm_apply_apply] using (T.symm.continuous.tendsto (T p))
  obtain ⟨d,dp,mem⟩ := Metric.mem_nhds_iff.mp (back.eventually near)
  refine ⟨min d b,lt_min dp bp,fun x hx => ?_⟩
  have d1 := hx.trans_le (min_le_left _ _)
  have d2 := hx.trans_le (min_le_right _ _)
  have n := mem (show T x.val∈ball (T p) d from d1)
  change T.symm (T x.val)∈e.source → -ε<A*(‖e (T.symm (T x.val))‖^2-1) at n
  rw [T.symm_apply_apply] at n
  exact (n (coord x d2)).trans_le ((le_max_right _ _).trans_eq (formula x d2).symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_ball_subharmonic_barrier
