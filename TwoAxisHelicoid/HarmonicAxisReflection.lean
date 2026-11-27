import TwoAxisHelicoid.HarmonicComplexCoefficient
import TwoAxisHelicoid.SimilaritySymmetry
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace TwoAxisHelicoid
open Complex Set Filter Metric InnerProductSpace
open scoped Topology ComplexConjugate

theorem complex_reflected_hasDerivAt {F : ℂ → ℂ} {z v : ℂ} (h : HasDerivAt F v (conj z)) :
    HasDerivAt (fun w => conj (F (conj w))) (conj v) z := by
  have hc : Tendsto (fun w : ℂ => conj w) (𝓝[≠] z) (𝓝[≠] (conj z)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_conj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    intro he
    apply hw
    change w = z
    simpa only [starRingEnd_self_apply] using congrArg (starRingEnd ℂ) (show conj w = conj z from he)
  have ht := continuous_conj.continuousAt.tendsto.comp (h.tendsto_slope.comp hc)
  apply hasDerivAt_iff_tendsto_slope.mpr
  change Tendsto (fun w => slope (fun x => conj (F (conj x))) z w) _ _
  simpa only [Function.comp_def,slope_def_field,map_div₀,map_sub,starRingEnd_self_apply] using ht

/-- Schwarz reflection for a harmonic coordinate on a disk vanishing on
its real diameter. The conclusion holds on both sides of the axis. -/
theorem harmonic_zero_diameter_reflection {u : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicOnNhd u (ball 0 R)) (hzero : ∀ x : ℝ, (x:ℂ) ∈ ball 0 R → u x = 0) :
    ∀ z ∈ ball (0:ℂ) R, u (conj z) = -u z := by
  obtain ⟨F,hF,hre⟩ := hu.exists_analyticOnNhd_ball_re_eq
  have hconj {z : ℂ} (hz : z ∈ ball (0:ℂ) R) : conj z ∈ ball (0:ℂ) R := by
    simpa [mem_ball,dist_zero_right] using hz
  let K := fun w => F w+conj (F (conj w))
  have hK : AnalyticOnNhd ℂ K (ball (0:ℂ) R) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    exact fun z hz => ((hF z hz).differentiableAt.add
      (complex_reflected_hasDerivAt (hF _ (hconj hz)).differentiableAt.hasDerivAt).differentiableAt
      ).differentiableWithinAt
  have hreal : ∀ᶠ (x : ℝ) in 𝓝[≠] (0:ℝ), K (x:ℂ) = 0 := by
    have ht : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[≠] 0) (𝓝 (0:ℂ)) := by
      simpa using (continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [ht.eventually (ball_mem_nhds (0:ℂ) hR)] with x hx
    have he : (F (x : ℂ)).re = 0 := (hre hx).trans (hzero x hx)
    change F x+conj (F (conj (x:ℂ))) = 0
    rw [conj_ofReal,Complex.add_conj,he]
    simp
  have ht : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[≠] 0) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using (continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact ofReal_ne_zero.mpr hx
  have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), K z = 0 := by
    intro h
    obtain ⟨x,hx,hn⟩ := (hreal.and (ht.eventually h)).exists
    exact hn hx
  have hall := hK.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball (0:ℂ) R).isPreconnected
    (mem_ball_self hR) hfreq
  intro z hz
  have he := congrArg Complex.re (hall hz)
  change (F z+conj (F (conj z))).re = 0 at he
  rw [add_re,conj_re] at he
  linarith [show (F z).re = u z from hre hz,show (F (conj z)).re = u (conj z) from hre (hconj hz)]

/-- Real horizontal coordinate and zero transverse coordinates on the
diameter give the actual ambient half-turn, pointwise on the disk. -/
theorem harmonic_axis_chart_reflects {X : ℂ → Fin 3 → ℝ} {R : ℝ} (hR : 0 < R)
    (h : ∀ j, HarmonicOnNhd (fun z => X z j) (ball (0:ℂ) R))
    (hx : ∀ z ∈ ball (0:ℂ) R, X z 0 = z.re)
    (ha : ∀ x : ℝ, (x:ℂ) ∈ ball 0 R → X x = ![x,0,0]) :
    ∀ z ∈ ball (0:ℂ) R, X (conj z) = halfTurnX (X z) := by
  intro z hz
  have hz' : conj z ∈ ball (0:ℂ) R := by simpa [mem_ball,dist_zero_right] using hz
  have he (j : Fin 3) (hj : j ≠ 0) : X (conj z) j = -X z j :=
    harmonic_zero_diameter_reflection hR (h j) (fun x hxb => by
      rw [ha x hxb]
      fin_cases j <;> simp_all) z hz
  funext j
  fin_cases j
  · change X (conj z) 0 = X z 0
    rw [hx _ hz',hx _ hz,conj_re]
  · exact he 1 (by decide)
  · exact he 2 (by decide)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_axis_chart_reflects
