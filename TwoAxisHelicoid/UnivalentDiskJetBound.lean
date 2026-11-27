import TwoAxisHelicoid.UnivalentRescaledDisks
import TwoAxisHelicoid.HolomorphicDerivativeGrowth
import TwoAxisHelicoid.EntirePreSchwarzianRigidity
import TwoAxisHelicoid.LocallyBoundedChartLimits
import TwoAxisHelicoid.UnivalentHolomorphicLimits

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function
open scoped Topology

/-- A sequence of normalized univalent blow-ups of increasing radii
would converge to an entire univalent function with two prescribed jets
and bounded logarithmic derivative. -/
theorem univalent_rescaled_disks_impossible
    (F : ℕ → ℂ → ℂ) (good : ∀ n : ℕ, UnivalentRescaledDisk (F n) ((n:ℝ)+1)) : False := by
  classical
  let l := Ultrafilter.of (atTop : Filter ℕ)
  have co : (l : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
  have cover (R : ℝ) : ∀ᶠ (n : ℕ) in (l : Filter ℕ), R<(n:ℝ)+1 := by
    obtain ⟨N,hN⟩ := exists_nat_gt R
    exact ((eventually_ge_atTop N).filter_mono co).mono fun n hn => by
      have := (Nat.cast_le.mpr hn : (N:ℝ)≤n)
      linarith
  have onDisk (R : ℝ) (rp : 0<R) : ∀ᶠ n in (l : Filter ℕ),
      DifferentiableOn ℂ (F n) (ball 0 R) ∧ ∀ z∈ball (0:ℂ) R, ‖F n z‖≤1+Real.exp (2*R)*R := by
    filter_upwards [cover R] with n hn
    let sub := ball_subset_ball (x:=(0:ℂ)) hn.le
    have an := (good n).analytic.mono sub
    refine ⟨an.differentiableOn,fun z hz => ?_⟩
    have v := holomorphic_value_growth (f:=F n) (by norm_num : (0:ℝ)≤2) an
      (fun w hw => (good n).estimate w (sub hw)) hz
    simp only [(good n).origin,norm_zero,(good n).first,norm_one,one_mul,zero_add] at v
    linarith
  have pt (z : ℂ) : ∃ y : ℂ, Tendsto (fun n => F n z) (l : Filter ℕ) (𝓝 y) := by
    let R := ‖z‖+1
    have rp : 0<R := by dsimp [R]; positivity
    have hz : z∈ball (0:ℂ) R := mem_ball_zero_iff.mpr (by dsimp [R]; linarith)
    obtain ⟨y,_,h⟩ := (isCompact_closedBall (0:ℂ) (1+Real.exp (2*R)*R)).ultrafilter_le_nhds'
      (l.map fun n => F n z) ((onDisk R rp).mono fun n hi => mem_closedBall_zero_iff.mpr (hi.2 z hz))
    exact ⟨y,h⟩
  choose f point using pt
  have chart (R : ℝ) (rp : 0<R) := bounded_chart_limit_of_point_limits l F (f:=f) isOpen_ball
    (by positivity : 0<1+Real.exp (2*R)*R) (onDisk R rp) (fun w _ => point w)
  have jets (R : ℝ) (rp : 0<R) := by
    let U := ball (0:ℂ) R
    have first := (chart R rp).1.deriv ((onDisk R rp).mono fun _ h => h.1) isOpen_ball
    have d : ∀ᶠ n in (l : Filter ℕ), DifferentiableOn ℂ (deriv (F n)) U := (cover R).mono fun n hn =>
      (show AnalyticOnNhd ℂ (deriv (F n)) U from fun w hw => ((good n).analytic _ (ball_subset_ball hn.le hw)).deriv).differentiableOn
    exact And.intro first (first.deriv d isOpen_ball)
  have z0 : (0:ℂ)∈ball 0 (1:ℝ) := mem_ball_self one_pos
  have first0 : deriv f 0=1 := tendsto_nhds_unique ((jets 1 one_pos).1.tendsto_at z0)
    (tendsto_const_nhds.congr fun n => (good n).first.symm)
  have second0 : deriv (deriv f) 0=1 := tendsto_nhds_unique ((jets 1 one_pos).2.tendsto_at z0)
    (tendsto_const_nhds.congr fun n => (good n).second.symm)
  have analytic (z : ℂ) : AnalyticAt ℂ f z := (chart (‖z‖+1) (by positivity)).2 z (mem_ball_zero_iff.mpr (by linarith))
  have inj : Injective f := by
    intro x y eq
    let R := max ‖x‖ ‖y‖+1
    have rp : 0<R := by dsimp [R]; positivity
    have insideX : x∈ball (0:ℂ) R := mem_ball_zero_iff.mpr (by dsimp [R]; linarith [le_max_left ‖x‖ ‖y‖])
    have insideY : y∈ball (0:ℂ) R := mem_ball_zero_iff.mpr (by dsimp [R]; linarith [le_max_right ‖x‖ ‖y‖])
    apply nonconstant_univalent_limit_injective isOpen_ball (convex_ball (0:ℂ) R).isPreconnected (chart R rp).1
      ((cover R).mono fun n hn => ⟨(good n).analytic.differentiableOn.mono (ball_subset_ball hn.le),
        (good n).injective.mono (ball_subset_ball hn.le)⟩) _ insideX insideY eq
    intro b same
    have germ : f =ᶠ[𝓝 (0:ℂ)] fun _ => b := by
      filter_upwards [ball_mem_nhds 0 rp] with z hz using same hz
    exact one_ne_zero (first0.symm.trans (germ.deriv_eq.trans (deriv_const 0 b)))
  apply normalized_entire_preSchwarzian_impossible analytic inj first0 second0
  intro z
  let R := ‖z‖+1
  have rp : 0<R := by dsimp [R]; positivity
  have hz : z∈ball (0:ℂ) R := mem_ball_zero_iff.mpr (by dsimp [R]; linarith)
  exact le_of_tendsto_of_tendsto ((jets R rp).2.tendsto_at hz).norm
    (tendsto_const_nhds.mul ((jets R rp).1.tendsto_at hz).norm)
    ((cover R).mono fun n hn => (good n).estimate z (ball_subset_ball hn.le hz))

/-- A universal finite bound on the central pre-Schwarzian of a
univalent function on the unit disk. No estimate on its range is needed. -/
theorem univalent_unit_disk_jet_bound : ∃ C : ℝ, 0<C ∧ ∀ f : ℂ → ℂ,
    AnalyticOnNhd ℂ f (ball 0 1) → InjOn f (ball 0 1) → ‖deriv (deriv f) 0/deriv f 0‖≤C := by
  by_contra! fail
  have disks (n : ℕ) : ∃ F : ℂ → ℂ, UnivalentRescaledDisk F ((n:ℝ)+1) := by
    obtain ⟨f,hol,inj,h⟩ := fail (4*((n:ℝ)+1)) (by positivity)
    exact rescale_large_univalent_jet hol inj (by positivity) h
  choose F good using disks
  exact univalent_rescaled_disks_impossible F good

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.univalent_unit_disk_jet_bound
