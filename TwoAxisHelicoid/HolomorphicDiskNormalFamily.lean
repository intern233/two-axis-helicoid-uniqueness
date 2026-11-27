import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- Montel compactness for bounded holomorphic maps, allowing the
domains of the maps to exhaust the eventual open domain. Schwarz on
each coordinate disk gives a uniform modulus of continuity; compactness
of the target closed disk supplies simultaneous ultrafilter limits. -/
theorem bounded_holomorphic_disk_normal_limit {ι : Type*} (l : Ultrafilter ι) (F : ι → ℂ → ℂ) {U : Set ℂ}
    (localBound : ∀ x∈U, ∃ r : ℝ, 0<r ∧ ball x r⊆U ∧
      ∀ᶠ i in (l : Filter ι), DifferentiableOn ℂ (F i) (ball x r) ∧ MapsTo (F i) (ball x r) (closedBall 0 1)) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f (l : Filter ι) U ∧ AnalyticOnNhd ℂ f U ∧ MapsTo f U (closedBall 0 1) := by
  classical
  have point (x : ℂ) (hx : x∈U) : ∃ y∈closedBall (0:ℂ) 1, Tendsto (fun i => F i x) (l : Filter ι) (𝓝 y) := by
    obtain ⟨r,rp,_,ev⟩ := localBound x hx
    exact (isCompact_closedBall (0:ℂ) 1).ultrafilter_le_nhds' (l.map (fun i => F i x))
      (ev.mono fun i hi => hi.2 (mem_ball_self rp))
  choose g bounded limit using point
  let f := fun x => if h : x∈U then g x h else 0
  have lim (x : ℂ) (hx : x∈U) : Tendsto (fun i => F i x) (l : Filter ι) (𝓝 (f x)) := by
    simpa only [f,dite_eq_left hx] using limit x hx
  have conv : TendstoLocallyUniformlyOn F f (l : Filter ι) U := by
    apply Metric.tendstoLocallyUniformlyOn_iff.mpr
    intro ε ep x hx
    obtain ⟨r,rp,sub,ev⟩ := localBound x hx
    let C := 2/r
    have lip : ∀ᶠ i in (l : Filter ι), ∀ y∈ball x r, dist (F i y) (F i x)≤C*dist y x := by
      filter_upwards [ev] with i hi
      have inner : MapsTo (F i) (ball x r) (closedBall (F i x) 2) := by
        intro z hz
        have two := dist_triangle (F i z) 0 (F i x)
        rw [dist_zero_right,dist_zero_left] at two
        have bz := mem_closedBall_zero_iff.mp (hi.2 hz)
        have bx := mem_closedBall_zero_iff.mp (hi.2 (mem_ball_self rp))
        exact mem_closedBall.mpr (by linarith)
      exact fun y hy => dist_le_div_mul_dist_of_mapsTo_ball hi.1 inner hy
    have lipf (y : ℂ) (hy : y∈ball x r) : dist (f y) (f x)≤C*dist y x :=
      le_of_tendsto ((lim y (sub hy)).dist (lim x hx)) (lip.mono fun _ h => h y hy)
    let S := ball x r ∩ {y : ℂ | C*dist y x<ε/3}
    have op : IsOpen S := isOpen_ball.inter (isOpen_lt (continuous_const.mul (continuous_id.dist continuous_const)) continuous_const)
    have xs : x∈S := ⟨mem_ball_self rp,by simpa using (div_pos ep (by norm_num : (0:ℝ)<3))⟩
    refine ⟨S,mem_nhdsWithin_of_mem_nhds (op.mem_nhds xs),?_⟩
    filter_upwards [lip,(Metric.tendsto_nhds.mp (lim x hx) (ε/3) (by positivity))] with i bound close
    intro y hy
    have small : C*dist y x<ε/3 := hy.2
    have t := dist_triangle (f y) (f x) (F i y)
    have t' := dist_triangle (f x) (F i x) (F i y)
    rw [dist_comm (f x) (F i x),dist_comm (F i x) (F i y)] at t'
    linarith [lipf y hy.1,bound y hy.1]
  refine ⟨f,conv,?_,fun x hx => by simpa only [f,dite_eq_left hx] using bounded x hx⟩
  intro x hx
  obtain ⟨r,rp,sub,ev⟩ := localBound x hx
  exact ((conv.mono sub).differentiableOn (ev.mono fun _ h => h.1) isOpen_ball).analyticAt
    (ball_mem_nhds x rp)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_holomorphic_disk_normal_limit
