import TwoAxisHelicoid.PlanarDriftBarrier
import TwoAxisHelicoid.EllipticBarrierComparison
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace TwoAxisHelicoid
open Complex Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Topology InnerProductSpace

private theorem inward_segment_radius (c y : ℂ) (s : ℝ) :
    dist (y+s • (c-y)) c = |1-s| * dist y c := by
  rw [dist_eq_norm,dist_eq_norm]
  have e : y+s • (c-y)-c = (1-s) • (y-c) := by
    rw [sub_smul,one_smul,smul_sub,smul_sub]
    abel
  rw [e,norm_smul,Real.norm_eq_abs]

/-- On a positive disk, a boundary zero of a subsolution with bounded
drift has strictly positive derivative toward the center. The comparison
is made on the closed outer half-annulus of the disk. -/
theorem planar_drift_hopf_boundary {c y : ℂ} {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hy : dist y c = r)
    {f : ℂ → ℝ} (hf : ∀ z ∈ closedBall c r, AnalyticAt ℝ f z)
    (nn : ∀ z ∈ closedBall c r, 0 ≤ f z) (hp : ∀ z ∈ ball c r, 0 < f z) (hzero : f y = 0)
    (sub : ∀ z ∈ closedBall c r, (Δ f) z ≤ K*(|planePartial 1 f z|+|planePartial I f z|+f z)) :
    0 < planePartial (c-y) f y := by
  let S := {z : ℂ | r/2 ≤ dist z c ∧ dist z c ≤ r}
  have comp : IsCompact S := (isCompact_closedBall c r).inter_left
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  obtain ⟨k,hk,bar⟩ := exists_strict_planar_radial_barrier c hK hr
  let B := planarRadialBarrier c k r
  have ha (z : ℂ) : AnalyticAt ℝ B z := planarRadialBarrier_analytic c z k r
  have sphere' (z : ℂ) (hz : z ∈ sphere c (r/2)) : z ∈ ball c r := by
    have eq := mem_sphere.mp hz
    exact mem_ball.mpr (by linarith)
  have nonempty : (sphere c (r/2)).Nonempty := by
    refine ⟨y+(1/2:ℝ) • (c-y),mem_sphere.mpr ?_⟩
    rw [inward_segment_radius,hy]
    norm_num
    ring
  obtain ⟨p,hpS,min⟩ := (isCompact_sphere c (r/2)).exists_isMinOn nonempty (f := f)
    (fun w hw => (hf w (ball_subset_closedBall (sphere' w hw))).continuousAt.continuousWithinAt)
  have he : 0 < f p := hp p (sphere' p hpS)
  have compB : ∀ z ∈ S, f p*B z ≤ f z := by
    apply analytic_plane_strict_barrier_comparison comp f B hK he
        (fun z hz => hf z hz.2) (fun z _ => ha z)
    · intro z hz hn
      by_cases hi : dist z c = r/2
      · have v : B z ≤ 1 := by
          rw [show B z = _ from planarRadialBarrier_value c z k r]
          exact (sub_le_self _ (Real.exp_pos _).le).trans (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (dist z c)]))
        exact (mul_le_of_le_one_right he.le v).trans (min (mem_sphere.mpr hi))
      by_cases ho : dist z c = r
      · have vz : B z = 0 := (planar_radial_barrier_inward hr hk ho).1
        rw [vz,mul_zero]
        exact nn z hz.2
      have o : IsOpen ({w : ℂ | r/2 < dist w c} ∩ ball c r) := (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter isOpen_ball
      have hm : z ∈ {w : ℂ | r/2 < dist w c} ∩ ball c r := ⟨hz.1.lt_of_ne (fun e => hi e.symm),hz.2.lt_of_ne ho⟩
      exact (hn (mem_interior_iff_mem_nhds.mpr (mem_of_superset (o.mem_nhds hm)
        (fun w hw => ⟨hw.1.le,(mem_ball.mp hw.2).le⟩)))).elim
    · intro z hz
      exact sub z (interior_subset hz).2
    · intro z hz
      exact bar z (interior_subset hz).1 (interior_subset hz).2
  have ymem : y ∈ closedBall c r := mem_closedBall.mpr hy.le
  let v := c-y
  let h := fun s : ℝ => f (y+s • v)-f p*B (y+s • v)
  have h0 : h 0 = 0 := by simp [h,hzero,(planar_radial_barrier_inward hr hk hy).1,B]
  have df : HasDerivAt (fun s : ℝ => f (y+s • v)) (planePartial v f y) 0 := by
    have d := parameter_line_hasDerivAt (z := y) (v := v) (t := 0) (show DifferentiableAt ℝ f (y+(0:ℝ) • v) by simpa using (hf y ymem).differentiableAt)
    simpa only [zero_smul,add_zero] using d
  have db : HasDerivAt (fun s : ℝ => B (y+s • v)) (planePartial v B y) 0 := by
    simpa only [zero_smul,add_zero] using parameter_line_hasDerivAt (z := y) (v := v) (t := 0) (ha _).differentiableAt
  have dh : HasDerivAt h (planePartial v f y-f p*planePartial v B y) 0 := df.sub (db.const_mul _)
  have nonneg : 0 ≤ planePartial v f y-f p*planePartial v B y := by
    apply le_of_tendsto_of_tendsto (g := slope h 0) (f := fun _ : ℝ => (0:ℝ))
      (b := 𝓝[>] (0:ℝ)) tendsto_const_nhds (hasDerivAt_iff_tendsto_slope_left_right.mp dh).2
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with s hs hsmall
    change 0 < s at hs
    have e : dist (y+s • v) c = (1-s)*r := by
      change dist (y+s • (c-y)) c = _
      rw [inward_segment_radius,hy,abs_of_pos (by linarith)]
    have inS : y+s • v ∈ S := by
      change r/2 ≤ _ ∧ _ ≤ r
      rw [e]
      constructor <;> nlinarith
    rw [slope_def_field,h0,sub_zero,sub_zero]
    exact div_nonneg (sub_nonneg.mpr (compB _ inS)) hs.le
  have pos := mul_pos he (planar_radial_barrier_inward hr hk hy).2
  change 0 < planePartial v f y
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planar_drift_hopf_boundary
