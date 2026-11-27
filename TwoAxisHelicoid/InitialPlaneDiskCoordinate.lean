import TwoAxisHelicoid.ExtremalDiskCoordinates

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- A branch of the square root of a translated plane coordinate
has open image disjoint from its negative. An inversion about the
opposite of one interior image point gives a bounded univalent map. -/
theorem bounded_injective_coordinate_of_proper_plane_domain {U : Set ℂ}
    (op : IsOpen U) (simply : IsSimplyConnected U) (proper : U≠univ) {p : ℂ} (hp : p∈U) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ MapsTo f U complexUnitDisk ∧ InjOn f U ∧ ∀ z∈U, deriv f z≠0 := by
  obtain ⟨a,miss⟩ := (ne_univ_iff_exists_notMem U).mp proper
  let H := fun z : ℂ => z-a
  have ah : AnalyticOnNhd ℂ H U := fun _ _ => analyticAt_id.sub analyticAt_const
  have nz (z : ℂ) (hz : z∈U) : H z≠0 := sub_ne_zero.mpr (fun e => miss (e ▸ hz))
  obtain ⟨q,cq,sq⟩ := exists_continuousOn_pow_eq simply op ah.continuousOn
    (show 0∉H '' U from fun ⟨z,hz,e⟩ => nz z hz e) (two_ne_zero : (2:ℕ)≠0)
  have analytic := analytic_continuous_square_root op cq ah (fun z _ => sq z) nz
  have qne (z : ℂ) (hz : z∈U) : q z≠0 := fun h => nz z hz ((sq z).symm.trans (by rw [h]; norm_num))
  have regular (z : ℂ) (hz : z∈U) : deriv q z≠0 := by
    have d := ((analytic z hz).differentiableAt.hasDerivAt.pow 2).deriv
    have e : (fun w => q w^2)=H := funext sq
    change deriv (fun w => q w^2) z=_ at d
    rw [e,show deriv H z=1 from ((hasDerivAt_id z).sub_const a).deriv] at d
    intro zero
    simp [zero] at d
  have inj : Function.Injective q := by
    intro x y h
    have eq : H x=H y := (sq x).symm.trans ((congrArg (fun w : ℂ => w^2) h).trans (sq y))
    simpa only [H,sub_left_inj] using eq
  have opposite {x y : ℂ} (hx : x∈U) (eq : q x= -q y) : False := by
    have same : H x=H y := by rw [← sq,← sq,eq,neg_sq]
    have xy : x=y := by simpa only [H,sub_left_inj] using same
    rw [← xy] at eq
    apply qne x hx
    linear_combination eq / 2
  have nb : q '' U∈𝓝 (q p) := by
    rw [← (analytic p hp).hasStrictDerivAt.map_nhds_eq (regular p hp)]
    exact image_mem_map (op.mem_nhds hp)
  obtain ⟨r,rp,rad⟩ := Metric.nhds_basis_ball.mem_iff.mp nb
  have gap (z : ℂ) (hz : z∈U) : r≤‖q z+q p‖ := by
    by_contra! h
    have inside : -q z∈ball (q p) r := by
      change dist (-q z) (q p)<r
      rwa [dist_eq_norm,show -q z-q p= -(q z+q p) by abel,norm_neg]
    obtain ⟨x,hx,eq⟩ := rad inside
    exact opposite hx eq
  let c : ℂ := (r/2:ℝ)
  let f := fun z => c/(q z+q p)
  have cn : ‖c‖=r/2 := by rw [Complex.norm_real,Real.norm_of_nonneg (half_pos rp).le]
  have nc : c≠0 := norm_pos_iff.mp (cn.trans_gt (half_pos rp))
  have denom (z : ℂ) (hz : z∈U) := norm_pos_iff.mp (rp.trans_le (gap z hz))
  refine ⟨f,fun z hz => analyticAt_const.div ((analytic z hz).add analyticAt_const) (denom z hz),?_,?_,?_⟩
  · intro z hz
    apply mem_ball_zero_iff.mpr
    change ‖c/(q z+q p)‖<1
    rw [norm_div,cn,div_lt_one (rp.trans_le (gap z hz))]
    exact (half_lt_self rp).trans_le (gap z hz)
  · intro x _ y _ eq
    apply inj
    have h : (q x+q p)⁻¹=(q y+q p)⁻¹ := mul_left_cancel₀ nc (by simpa only [f,div_eq_mul_inv] using eq)
    exact add_right_cancel (inv_injective h)
  · intro z hz
    change deriv (fun w => c/(q w+q p)) z≠0
    rw [deriv_const_div c ((analytic z hz).differentiableAt.add_const _) (denom z hz),deriv_add_const]
    exact div_ne_zero (by simp [nc,regular z hz]) (pow_ne_zero _ (denom z hz))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_injective_coordinate_of_proper_plane_domain
