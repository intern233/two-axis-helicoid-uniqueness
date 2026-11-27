import TwoAxisHelicoid.SurfaceHarmonicComparison
import Mathlib.Analysis.Analytic.Uniqueness

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology Bornology InnerProductSpace

/-- A harmonic function on a bounded open plane domain is nonnegative
if its boundary lower limits are nonnegative, including at deleted points
where the function need not admit a continuous extension. -/
theorem bounded_domain_harmonic_nonneg {U : Set ℂ} (op : IsOpen U) (bounded : IsBounded U)
    {u : ℂ → ℝ} (harmonic : ∀ z∈U, HarmonicAt u z)
    (edge : ∀ z∈frontier U, ∀ e : ℝ, 0<e → ∀ᶠ w in 𝓝[U] z, -e≤u w) :
    ∀ z∈U, 0≤u z := by
  intro z hz
  by_contra! neg
  let e := -u z/2
  have ep : 0<e := by dsimp [e]; linarith
  let B := {w | w∈U ∧ u w≤ -e}
  let K := closure B
  have sub : B⊆U := fun _ h => h.1
  have compact : IsCompact K := (bounded.subset sub).isCompact_closure
  have inside : K⊆U := by
    intro x hx
    by_contra out
    have frontier : x∈frontier U := ⟨closure_mono sub hx,fun m => out (interior_subset m)⟩
    have near := (edge x frontier (e/2) (half_pos ep)).filter_mono (nhdsWithin_mono x sub)
    have : NeBot (𝓝[B] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
    have inp : ∀ᶠ w in 𝓝[B] x, w∈B := self_mem_nhdsWithin
    obtain ⟨w,hw,ineq⟩ := (inp.and near).exists
    have low : u w≤ -e := hw.2
    linarith
  let f := fun w => -u w-e
  have hfun (w : ℂ) (hw : w∈K) : HarmonicAt f w := (harmonic w (inside hw)).neg.sub (harmonicAt_const e)
  have bd (w : ℂ) (hw : w∈K) (outside : w∉interior K) : f w≤0 := by
    by_contra! high
    have low : u w< -e := by dsimp [f] at high; linarith
    have near := (harmonic w (inside hw)).1.continuousAt.eventually (Iio_mem_nhds low)
    apply outside (mem_interior_iff_mem_nhds.mpr ?_)
    filter_upwards [op.mem_nhds (inside hw),near] with x xin xl
    exact subset_closure (show x∈B from ⟨xin,xl.le⟩)
  have result := compact_boundary_maximum_principle compact
    (fun w hw => (hfun w hw).1.continuousAt.continuousWithinAt) bd
    (fun w hw _ mx => harmonic_eventually_constant_at_local_max (hfun w (interior_subset hw)) mx)
  have atZ := result z (subset_closure (show z∈B from ⟨hz,by dsimp [e]; linarith⟩))
  dsimp [f,e] at atZ
  linarith

/-- If the harmonic function is nonconstant on a larger connected
domain, the weak boundary lower bounds imply strict positivity inside
even when the bounded subdomain has several components. -/
theorem bounded_domain_harmonic_pos {U V : Set ℂ} (op : IsOpen U) (bounded : IsBounded U) (sub : U⊆V)
    (connected : IsPreconnected V) {u : ℂ → ℝ} (harmonic : ∀ z∈V, HarmonicAt u z)
    (nonzero : ∃ z∈V, u z≠0)
    (edge : ∀ z∈frontier U, ∀ e : ℝ, 0<e → ∀ᶠ w in 𝓝[U] z, -e≤u w) :
    ∀ z∈U, 0<u z := by
  have nonneg := bounded_domain_harmonic_nonneg op bounded (fun w hw => harmonic w (sub hw)) edge
  intro z hz
  apply lt_of_le_of_ne (nonneg z hz)
  intro zero
  have m : IsLocalMax (fun w => -u w) z := by
    filter_upwards [op.mem_nhds hz] with w hw
    exact neg_le_neg (zero ▸ nonneg w hw)
  have flat := harmonic_eventually_constant_at_local_max (harmonic z (sub hz)).neg m
  have germ : u =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [flat] with w eq
    exact (neg_inj.mp eq).trans zero.symm
  have an : AnalyticOnNhd ℝ u V := fun w hw => _root_.HarmonicAt.analyticAt (harmonic w hw)
  obtain ⟨y,hy,ne⟩ := nonzero
  exact ne (an.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const connected (sub hz) germ hy)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_domain_harmonic_nonneg
#print axioms TwoAxisHelicoid.bounded_domain_harmonic_pos
