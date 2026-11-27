import TwoAxisHelicoid.PlaneCircleWinding
import Mathlib.Topology.Piecewise

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology

/-- Degree of a circle-valued map on all sufficiently small positive
circles about a prescribed point. Its value at the point is immaterial. -/
def HasLocalWinding (F : ℂ → OrientationCircle) (p : ℂ) (n : ℤ) : Prop :=
  ∃ R : ℝ, 0<R ∧ ∀ r∈Ioo (0:ℝ) R,
    HasOrientationCircleDegree (fun a => F (p+r • orientationRay a)) n

theorem HasLocalWinding.congr {F G : ℂ → OrientationCircle} {p : ℂ} {n : ℤ}
    (h : HasLocalWinding F p n) (agreement : G=ᶠ[𝓝 p] F) : HasLocalWinding G p n := by
  obtain ⟨R,rp,degree⟩ := h
  obtain ⟨S,sp,inc⟩ := Metric.mem_nhds_iff.mp agreement
  refine ⟨min R S,lt_min rp sp,fun r hr => ?_⟩
  have eq : (fun a => G (p+r • orientationRay a))=(fun a => F (p+r • orientationRay a)) :=
    funext fun a => inc (orientation_probe_point_mem_ball ⟨hr.1,hr.2.trans_le (min_le_right _ _)⟩ a)
  rw [eq]
  exact degree _ ⟨hr.1,hr.2.trans_le (min_le_left _ _)⟩

theorem HasLocalWinding.sub {F G : ℂ → OrientationCircle} {p : ℂ} {n m : ℤ}
    (h : HasLocalWinding F p n) (k : HasLocalWinding G p m) :
    HasLocalWinding (fun z => F z-G z) p (n-m) := by
  obtain ⟨R,rp,deg⟩ := h
  obtain ⟨S,sp,deg'⟩ := k
  exact ⟨min R S,lt_min rp sp,fun _ hr => (deg _ ⟨hr.1,hr.2.trans_le (min_le_left _ _)⟩).sub
    (deg' _ ⟨hr.1,hr.2.trans_le (min_le_right _ _)⟩)⟩

theorem HasLocalWinding.zsmul {F : ℂ → OrientationCircle} {p : ℂ} {n : ℤ}
    (h : HasLocalWinding F p n) (k : ℤ) : HasLocalWinding (fun z => k • F z) p (k*n) := by
  obtain ⟨R,rp,deg⟩ := h
  exact ⟨R,rp,fun _ hr => (deg _ hr).zsmul k⟩

private theorem direction_winding_at_center (p : ℂ) :
    HasLocalWinding (fun z => planeOrientationDirection (z-p)) p 1 := by
  refine ⟨1,one_pos,fun r hr => ?_⟩
  simp only [add_sub_cancel_left,planeOrientationDirection_scaled_ray hr.1]
  exact orientationCircle_degree_id

private theorem direction_winding_away {p q : ℂ} (ne : q≠p) :
    HasLocalWinding (fun z => planeOrientationDirection (z-p)) q 0 := by
  obtain ⟨R,rp,inc⟩ := Metric.mem_nhds_iff.mp (isOpen_compl_singleton.mem_nhds ne)
  refine ⟨R,rp,fun r hr => disk_boundary_winding_zero (F := fun z => planeOrientationDirection (z-p)) (p := q) hr.1.le ?_⟩
  intro z hz
  have nz : z≠p := inc (closedBall_subset_ball hr.2 hz)
  exact ((planeOrientationDirection_continuousAt (sub_ne_zero.mpr nz)).comp (f := fun w : ℂ => w-p)
    (continuousAt_id.sub continuousAt_const)).continuousWithinAt

private theorem exterior_direction_winding {p : ℂ} {R : ℝ} (inside : ‖p‖<R) :
    HasOrientationCircleDegree (fun a => planeOrientationDirection (R • orientationRay a-p)) 1 := by
  have rp := (norm_nonneg p).trans_lt inside
  have cc : Continuous (fun a => R • orientationRay a) := orientationRay_continuous.const_smul R
  apply circle_degree_small_perturbation (cc.sub continuous_const) cc
  · simp only [planeOrientationDirection_scaled_ray rp]
    exact orientationCircle_degree_id
  · intro a
    change ‖R • orientationRay a-p-R • orientationRay a‖<‖R • orientationRay a‖
    rw [show R • orientationRay a-p-R • orientationRay a= -p by abel,norm_neg,norm_smul,
      Real.norm_of_nonneg rp.le,orientationRay_norm,mul_one]
    exact inside

/-- On a disk containing a finite set of singularities, the degree on
the outer circle is the sum of the actual local winding numbers. The
map needs only continuity off the finite set. -/
theorem winding_sum_of_finite_plane_singularities (S : Finset ℂ) (F : ℂ → OrientationCircle) (n : ℂ → ℤ)
    (cont : ContinuousOn F (S : Set ℂ)ᶜ) (loc : ∀ p∈S, HasLocalWinding F p (n p))
    {R : ℝ} (rp : 0<R) (inside : ∀ p∈S, ‖p‖<R) :
    HasOrientationCircleDegree (fun a => F (R • orientationRay a)) (∑ p∈S, n p) := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
    have cf : Continuous F := by simpa using cont
    simpa only [Finset.sum_empty,zero_add] using
      (disk_boundary_winding_zero (p := (0:ℂ)) rp.le (cf.continuousOn (s := closedBall 0 R)))
  | @insert p S hp ih =>
    let angle := fun z : ℂ => planeOrientationDirection (z-p)
    let K := fun z => F z-n p • angle z
    have pin := inside p (Finset.mem_insert_self _ _)
    have atp : HasLocalWinding K p 0 := by
      simpa only [mul_one,sub_self,K,angle] using
        (loc p (Finset.mem_insert_self _ _)).sub ((direction_winding_at_center p).zsmul (n p))
    obtain ⟨T,tp,winds⟩ := atp
    have nb : (S : Set ℂ)ᶜ∩ball (0:ℂ) R ∈ 𝓝 p :=
      inter_mem (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hp)
        (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using pin))
    obtain ⟨D,dp,inc⟩ := Metric.mem_nhds_iff.mp nb
    let r := min T D/2
    have positive : 0<r := half_pos (lt_min tp dp)
    have ltmin : r<min T D := half_lt_self (lt_min tp dp)
    have sep {z : ℂ} (hz : z∈closedBall p r) : z∉S ∧ ‖z‖<R := by
      have h := inc (closedBall_subset_ball (ltmin.trans_le (min_le_right _ _)) hz)
      exact ⟨h.1,by simpa only [mem_ball,dist_zero_right] using h.2⟩
    obtain ⟨B,same⟩ := fill_zero_winding_circle positive (winds r ⟨positive,ltmin.trans_le (min_le_left _ _)⟩)
    let G := (ball p r).piecewise B K
    have cG : ContinuousOn G (S : Set ℂ)ᶜ := by
      apply ContinuousOn.piecewise (fun z hz => same z (frontier_ball_subset_sphere hz.2)) B.continuous.continuousOn
      intro z hz
      have off : z∉ball p r := by
        change z∈(ball p r)ᶜ
        simpa only [isOpen_ball.isClosed_compl.closure_eq] using hz.2
      have zne : z≠p := fun e => off (e ▸ mem_ball_self positive)
      have notin : z∈((insert p S : Finset ℂ) : Set ℂ)ᶜ := by
        intro mem
        exact (Finset.mem_insert.mp mem).elim zne hz.1
      have fz := cont.continuousAt ((insert p S).finite_toSet.isClosed.isOpen_compl.mem_nhds notin)
      exact (fz.sub (((planeOrientationDirection_continuousAt (sub_ne_zero.mpr zne)).comp (f := fun w : ℂ => w-p)
        (continuousAt_id.sub continuousAt_const)).const_smul (n p))).continuousWithinAt
    have other (q : ℂ) (hq : q∈S) : HasLocalWinding G q (n q) := by
      have qne : q≠p := fun e => hp (e ▸ hq)
      have h : HasLocalWinding K q (n q) := by
        simpa only [K,angle,mul_zero,sub_zero] using
          (loc q (Finset.mem_insert_of_mem hq)).sub ((direction_winding_away qne).zsmul (n p))
      apply h.congr
      have out : q∉closedBall p r := fun mem => (sep mem).1 hq
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds out] with z hz
      exact (ball p r).piecewise_eq_of_notMem B K (fun h => hz (ball_subset_closedBall h))
    have outer := ih G cG other (fun q hq => inside q (Finset.mem_insert_of_mem hq))
    have restore (a : OrientationCircle) : F (R • orientationRay a)=
        G (R • orientationRay a)+n p • angle (R • orientationRay a) := by
      have nr : ‖R • orientationRay a‖=R := by simp only [norm_smul,orientationRay_norm,Real.norm_of_nonneg rp.le,mul_one]
      have outside : R • orientationRay a∉ball p r := fun h => nr.not_lt (sep (ball_subset_closedBall h)).2
      rw [show G (R • orientationRay a)=K (R • orientationRay a) from (ball p r).piecewise_eq_of_notMem B K outside]
      exact (sub_add_cancel _ _).symm
    rw [Finset.sum_insert hp,add_comm]
    convert outer.add ((exterior_direction_winding pin).zsmul (n p)) using 1
    · exact funext restore
    · rw [mul_one]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.winding_sum_of_finite_plane_singularities
