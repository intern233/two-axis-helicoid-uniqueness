import TwoAxisHelicoid.OrderedDriftContact
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected

namespace TwoAxisHelicoid
open Complex Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Topology

/-- Arbitrarily small disks within a specified side, tangent at the
boundary point. The boundary circle is included. -/
def HasInwardTangentDisksAt (S : Set ℂ) (z : ℂ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ (c : ℂ) (r : ℝ), 0<r ∧ dist z c=r ∧ closedBall c r ⊆ S ∩ ball z ε

private theorem drift_minimum_on_tangent_disks {S : Set ℂ} {f A B : ℂ → ℝ} {x : ℂ}
    (disks : HasInwardTangentDisksAt S x) (ha : AnalyticAt ℝ f x) (ca : ContinuousAt A x) (cb : ContinuousAt B x)
    (eq : ∀ᶠ z in 𝓝 x, (Δ f) z=A z*planePartial 1 f z+B z*planePartial I f z)
    (zero : f x=0) (flat : fderiv ℝ f x=0) (side : ∀ᶠ z in 𝓝 x, z ∈ S → 0≤f z) :
    f =ᶠ[𝓝 x] 0 := by
  let K := max |A x| |B x|+1
  have ak : |A x|<K := by dsimp [K]; linarith [le_max_left |A x| |B x|]
  have bk : |B x|<K := by dsimp [K]; linarith [le_max_right |A x| |B x|]
  have hk := (abs_nonneg (A x)).trans ak.le
  obtain ⟨R,hR,sub⟩ := Metric.mem_nhds_iff.mp (ha.eventually_analyticAt.and
    (eq.and (side.and ((ca.abs.eventually_lt continuousAt_const ak).and (cb.abs.eventually_lt continuousAt_const bk)))))
  obtain ⟨c,r,hr,distx,inside⟩ := disks R hR
  have an : AnalyticOnNhd ℝ f (ball x R) := fun _ hw => (sub hw).1
  have nonneg {w : ℂ} (hw : w ∈ closedBall c r) : 0 ≤ f w := (sub (inside hw).2).2.2.1 (inside hw).1
  have inequality {w : ℂ} (hw : w ∈ closedBall c r) :
      (Δ f) w ≤ K*(|planePartial 1 f w|+|planePartial I f w|+f w) := by
    obtain ⟨_,e,_,pa,pb⟩ := sub (inside hw).2
    rw [e]
    calc A w*planePartial 1 f w+B w*planePartial I f w
        ≤ |A w*planePartial 1 f w|+|B w*planePartial I f w| := add_le_add (le_abs_self _) (le_abs_self _)
      _ = |A w| *|planePartial 1 f w|+|B w| *|planePartial I f w| := by rw [abs_mul,abs_mul]
      _ ≤ K*|planePartial 1 f w|+K*|planePartial I f w| :=
        add_le_add (mul_le_mul_of_nonneg_right pa.le (abs_nonneg _)) (mul_le_mul_of_nonneg_right pb.le (abs_nonneg _))
      _ ≤ _ := by nlinarith [mul_nonneg hk (nonneg hw)]
  by_contra notZero
  have positive (w : ℂ) (hw : w ∈ ball c r) : 0<f w := by
    apply lt_of_le_of_ne (nonneg (ball_subset_closedBall hw))
    intro ew
    have ball' : ∀ᶠ v in 𝓝 w, v ∈ ball c r := isOpen_ball.mem_nhds hw
    have germ := analytic_planar_strong_minimum hk ew.symm
      (an w (inside (ball_subset_closedBall hw)).2).eventually_analyticAt
      (ball'.mono fun _ hv => nonneg (ball_subset_closedBall hv))
      (ball'.mono fun _ hv => inequality (ball_subset_closedBall hv))
    have vanish := an.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball (inside (ball_subset_closedBall hw)).2 germ
    exact notZero (Filter.mem_of_superset (ball_mem_nhds x hR) (fun _ hv => vanish hv))
  have hop := planar_drift_hopf_boundary hr hk distx (fun w hw => an w (inside hw).2)
    (fun _ hw => nonneg hw) positive zero (fun _ hw => inequality hw)
  simp [planePartial,flat] at hop

/-- At a boundary point with an interior tangent disk, a one-sided
solution of the linear drift equation that is tangent to zero has
identically zero germ. Both signs and both disk orientations are allowed. -/
theorem planar_drift_boundary_tangent_contact {S : Set ℂ} {f A B : ℂ → ℝ} {x : ℂ}
    (disks : HasInwardTangentDisksAt S x) (ha : AnalyticAt ℝ f x) (ca : ContinuousAt A x) (cb : ContinuousAt B x)
    (eq : ∀ᶠ z in 𝓝 x, (Δ f) z=A z*planePartial 1 f z+B z*planePartial I f z)
    (zero : f x=0) (flat : fderiv ℝ f x=0)
    (side : (∀ᶠ z in 𝓝 x, z ∈ S → 0≤f z) ∨ (∀ᶠ z in 𝓝 x, z ∈ S → f z≤0)) :
    f =ᶠ[𝓝 x] 0 := by
  rcases side with lo | hi
  · exact drift_minimum_on_tangent_disks disks ha ca cb eq zero flat lo
  have sol : ∀ᶠ z in 𝓝 x, (Δ (-f)) z=A z*planePartial 1 (-f) z+B z*planePartial I (-f) z := by
    filter_upwards [eq,ha.eventually_analyticAt] with z he hz
    rw [laplacian_neg,Pi.neg_apply,he]
    have negd (v : ℂ) : planePartial v (-f) z = -planePartial v f z :=
      congrArg (fun D : ℂ →L[ℝ] ℝ => D v) hz.differentiableAt.hasFDerivAt.neg.fderiv
    rw [negd,negd]
    ring
  have h := drift_minimum_on_tangent_disks (f := -f) disks ha.neg ca cb sol (by simp [zero])
    (by rw [ha.differentiableAt.hasFDerivAt.neg.fderiv,flat,neg_zero]) (hi.mono fun _ hv hS => neg_nonneg.mpr (hv hS))
  exact h.mono fun _ he => neg_eq_zero.mp he

/-- Each of the two vertical coordinate half-planes contains closed
interior tangent disks at every point of its boundary. -/
theorem vertical_half_planes_have_tangent_disks (x : ℂ) :
    HasInwardTangentDisksAt {w : ℂ | x.re ≤ w.re} x ∧ HasInwardTangentDisksAt {w : ℂ | w.re ≤ x.re} x := by
  have build (s : ℝ) (hs : s=1 ∨ s= -1) :
      HasInwardTangentDisksAt {w : ℂ | 0 ≤ s*(w.re-x.re)} x := by
    intro ε hε
    let r := ε/4
    have hr : 0<r := by dsimp [r]; positivity
    let c := x+((s*r:ℝ):ℂ)
    have dc : dist x c=r := by
      rw [dist_comm,dist_eq_norm]
      simp only [c,add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos hr]
      rcases hs with rfl | rfl <;> simp
    refine ⟨c,r,hr,dc,fun w hw => ⟨?_,?_⟩⟩
    · have d := (Complex.abs_re_le_norm (w-c)).trans (mem_closedBall_iff_norm.mp hw)
      rw [Complex.sub_re,show c.re=x.re+s*r by simp [c]] at d
      change 0≤s*(w.re-x.re)
      rcases hs with rfl | rfl <;> rcases abs_le.mp d with ⟨l,u⟩ <;> linarith
    · have dd := dist_triangle w c x
      rw [← dist_comm x c,dc] at dd
      exact mem_ball.mpr (by linarith [mem_closedBall.mp hw,show r=ε/4 from rfl])
  constructor
  · simpa only [one_mul,sub_nonneg] using build 1 (Or.inl rfl)
  · simpa only [neg_one_mul,neg_sub,sub_nonneg] using build (-1) (Or.inr rfl)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planar_drift_boundary_tangent_contact
#print axioms TwoAxisHelicoid.vertical_half_planes_have_tangent_disks
