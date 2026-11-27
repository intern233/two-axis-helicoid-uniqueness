import TwoAxisHelicoid.FinitePlaneWinding
import Mathlib.Analysis.Analytic.Order

namespace TwoAxisHelicoid
open Complex Filter Set Topology Metric
open scoped Topology

theorem HasLocalWinding.congr_punctured {F G : ℂ → OrientationCircle} {p : ℂ} {n : ℤ}
    (h : HasLocalWinding F p n) (eq : G=ᶠ[𝓝[≠] p] F) : HasLocalWinding G p n := by
  obtain ⟨R,rp,deg⟩ := h
  obtain ⟨S,sp,inc⟩ := Metric.mem_nhdsWithin_iff.mp eq
  refine ⟨min R S,lt_min rp sp,fun r hr => ?_⟩
  have agree (a : OrientationCircle) : G (p+r • orientationRay a)=F (p+r • orientationRay a) := by
    apply inc
    refine ⟨orientation_probe_point_mem_ball ⟨hr.1,hr.2.trans_le (min_le_right _ _)⟩ a,?_⟩
    exact fun e => smul_ne_zero hr.1.ne' (orientationRay_ne_zero a) (add_eq_left.mp e)
  rw [funext agree]
  exact deg _ ⟨hr.1,hr.2.trans_le (min_le_left _ _)⟩

theorem HasLocalWinding.add {F G : ℂ → OrientationCircle} {p : ℂ} {n m : ℤ}
    (h : HasLocalWinding F p n) (k : HasLocalWinding G p m) :
    HasLocalWinding (fun z => F z+G z) p (n+m) := by
  obtain ⟨R,rp,deg⟩ := h
  obtain ⟨S,sp,deg'⟩ := k
  exact ⟨min R S,lt_min rp sp,fun _ hr => (deg _ ⟨hr.1,hr.2.trans_le (min_le_left _ _)⟩).add
    (deg' _ ⟨hr.1,hr.2.trans_le (min_le_right _ _)⟩)⟩

theorem local_winding_zero_near_continuous {F : ℂ → OrientationCircle} {p : ℂ}
    (h : ∀ᶠ z in 𝓝 p, ContinuousAt F z) : HasLocalWinding F p 0 := by
  obtain ⟨R,rp,inc⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨R,rp,fun _ hr => disk_boundary_winding_zero hr.1.le
    (fun z hz => (inc (closedBall_subset_ball hr.2 hz)).continuousWithinAt)⟩

theorem planeOrientationDirection_mul {z w : ℂ} (nz : z≠0) (nw : w≠0) :
    planeOrientationDirection (z*w)=planeOrientationDirection z+planeOrientationDirection w := by
  have eq : z*w=(‖z‖*‖w‖) • orientationRay (planeOrientationDirection z+planeOrientationDirection w) := by
    rw [orientationRay_add,← smul_smul,← mul_smul_comm,planeOrientationDirection_reconstruct nw,
      ← smul_mul_assoc,planeOrientationDirection_reconstruct nz]
  rw [eq,planeOrientationDirection_scaled_ray (mul_pos (norm_pos_iff.mpr nz) (norm_pos_iff.mpr nw))]

private theorem direction_pow_succ {z : ℂ} (nz : z≠0) (n : ℕ) :
    planeOrientationDirection (z^(n+1))=(n+1) • planeOrientationDirection z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,planeOrientationDirection_mul (pow_ne_zero _ nz) nz,ih]
    exact (succ_nsmul _ _).symm

/-- The genuine analytic order of a local holomorphic map determines
its winding in any topological parameter chart, including at branch
points. Reversing the chart reverses the winding. -/
theorem local_holomorphic_order_winding (e : OpenPartialHomeomorph ℂ ℂ) {p : ℂ} (hp : p∈e.source)
    {s : ℤ} (orient : HasPlaneOrientationAt e p s) {f : ℂ → ℂ} (an : AnalyticAt ℂ f (e p)) {n : ℕ}
    (order : analyticOrderAt (fun w => f w-f (e p)) (e p)=((n+1:ℕ):ℕ∞)) :
    HasPlaneOrientationAt (f ∘ e) p (((n+1:ℕ):ℤ)*s) := by
  obtain ⟨g,analytic,nz,fac⟩ := ((an.sub analyticAt_const).analyticOrderAt_eq_natCast).mp order
  let θ := fun z => planeOrientationDirection (e z-e p)
  let φ := fun z => planeOrientationDirection (g (e z))
  have we : HasLocalWinding θ p s := orient
  have wg : HasLocalWinding φ p 0 := by
    apply local_winding_zero_near_continuous
    filter_upwards [e.open_source.mem_nhds hp,(e.continuousAt hp).eventually analytic.eventually_analyticAt,
      (e.continuousAt hp).eventually (analytic.continuousAt.eventually_ne nz)] with z source ag gn
    exact (planeOrientationDirection_continuousAt gn).comp (f := g ∘ e) (ag.continuousAt.comp (e.continuousAt source))
  have total := (we.zsmul ((n+1:ℕ):ℤ)).add wg
  rw [add_zero] at total
  change HasLocalWinding (fun z => planeOrientationDirection (f (e z)-f (e p))) p _
  apply total.congr_punctured
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hp),
    ((e.continuousAt hp).eventually fac).filter_mono nhdsWithin_le_nhds,
    ((e.continuousAt hp).eventually (analytic.continuousAt.eventually_ne nz)).filter_mono nhdsWithin_le_nhds]
    with z ne source fact unit
  have diff : e z-e p≠0 := sub_ne_zero.mpr (fun eq => ne (e.injOn source hp eq))
  change planeOrientationDirection (f (e z)-f (e p))=((n+1:ℕ):ℤ) • θ z+φ z
  change f (e z)-f (e p)=(e z-e p)^(n+1) • g (e z) at fact
  rw [fact,smul_eq_mul,planeOrientationDirection_mul (pow_ne_zero _ diff) unit,direction_pow_succ diff]
  simp only [θ,φ,natCast_zsmul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.local_holomorphic_order_winding
