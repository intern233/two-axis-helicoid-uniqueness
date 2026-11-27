import TwoAxisHelicoid.PlanarHopfBoundary

namespace TwoAxisHelicoid
open Complex Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Topology InnerProductSpace

/-- A nonnegative planar analytic subsolution with bounded drift and
zeroth-order coefficient cannot vanish at an interior point without
vanishing on a neighborhood. A disk of positivity tangent to the zero
set supplies the contradiction by the inward boundary derivative. -/
theorem analytic_planar_strong_minimum {f : ℂ → ℝ} {x : ℂ} {K : ℝ} (hK : 0 ≤ K) (hx : f x = 0)
    (hf : ∀ᶠ z in 𝓝 x, AnalyticAt ℝ f z) (hn : ∀ᶠ z in 𝓝 x, 0 ≤ f z)
    (hd : ∀ᶠ z in 𝓝 x, (Δ f) z ≤ K*(|planePartial 1 f z|+|planePartial I f z|+f z)) :
    f =ᶠ[𝓝 x] fun _ => 0 := by
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (hf.and (hn.and hd))
  by_contra h
  have freq : ∃ᶠ z in 𝓝 x, f z ≠ 0 := not_eventually.mp h
  obtain ⟨c,hc,hfc⟩ := (freq.and_eventually (ball_mem_nhds x (by positivity : 0<R/5))).exists
  change dist c x < R/5 at hfc
  let S := closedBall x (R/2)
  let Z := {w ∈ S | f w = 0}
  have small (z : ℂ) (hz : z ∈ S) : z ∈ ball x R := (mem_closedBall.mp hz).trans_lt (by linarith)
  have cl : IsClosed Z := isClosed_closedBall.isClosed_eq
    (fun z hz => (hball (small z hz)).1.continuousAt.continuousWithinAt) continuousOn_const
  have kz : IsCompact Z := (isCompact_closedBall x (R/2)).of_isClosed_subset cl (fun _ hz => hz.1)
  have xZ : x ∈ Z := ⟨mem_closedBall_self (by positivity),hx⟩
  obtain ⟨y,hy,hmin⟩ := kz.exists_isMinOn ⟨x,xZ⟩ (continuous_id.dist continuous_const).continuousOn
  let r := dist y c
  have near : r ≤ dist x c := hmin xZ
  have hr : 0 < r := dist_pos.mpr (fun heq => hc (heq ▸ hy.2))
  have smallBall (z : ℂ) (hz : z ∈ closedBall c r) : z ∈ S := by
    change dist z x ≤ R/2
    have bound := dist_triangle z c x
    have close := mem_closedBall.mp hz
    rw [dist_comm x c] at near
    linarith
  have pos (z : ℂ) (hz : z ∈ ball c r) : 0 < f z := by
    have hzS := smallBall z (ball_subset_closedBall hz)
    apply lt_of_le_of_ne (hball (small z hzS)).2.1
    intro nz
    have lower : r ≤ dist z c := hmin (show z ∈ Z from ⟨hzS,nz.symm⟩)
    exact (mem_ball.mp hz).not_ge lower
  have hop := planar_drift_hopf_boundary hr hK (show dist y c=r from rfl)
    (fun z hz => (hball (small z (smallBall z hz))).1)
    (fun z hz => (hball (small z (smallBall z hz))).2.1) pos hy.2
    (fun z hz => (hball (small z (smallBall z hz))).2.2)
  have miny : IsLocalMin f y := by
    filter_upwards [isOpen_ball.mem_nhds (small y hy.1)] with z hz
    exact hy.2 ▸ (hball hz).2.1
  simp [planePartial,miny.fderiv_eq_zero] at hop

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_planar_strong_minimum
