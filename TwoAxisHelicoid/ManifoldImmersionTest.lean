import TwoAxisHelicoid.SmoothImmersionLeftInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

/-- Smoothness into an actual immersed manifold can be tested after
its Euclidean immersion. In particular this checks smooth compatibility
of two surface structures which share the same regular ambient map. -/
theorem contMDiffAt_of_comp_regular_map
    {M N E E' A : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [ChartedSpace E M] [ChartedSpace E' N]
    {f : M → N} {F : N → A} {x : M}
    (hF : ContMDiffAt 𝓘(ℝ,E') 𝓘(ℝ,A) ∞ F (f x))
    (hi : Function.Injective (mfderiv 𝓘(ℝ,E') 𝓘(ℝ,A) F (f x)))
    (hf : ContinuousAt f x)
    (hcomp : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ (F ∘ f) x) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ f x := by
  let e := chartAt E x
  let e' := chartAt E' (f x)
  let y := e x
  let g := e' ∘ f ∘ e.symm
  have he : e.symm y = x := e.left_inv (mem_chart_source E x)
  have hy : y ∈ e.target := e.map_source (mem_chart_source E x)
  have he' : f x ∈ e'.source := mem_chart_source E' (f x)
  have hgval : g y = e' (f x) := by simp only [g,Function.comp_apply,he]
  have hfc : ContDiffAt ℝ ∞ (F ∘ e'.symm) (e' (f x)) := by
    simpa only [mfld_simps,contDiffWithinAt_univ] using! (contMDiffAt_iff.mp hF).2
  have hfd : HasMFDerivAt 𝓘(ℝ,E') 𝓘(ℝ,A) F (f x)
      (fderiv ℝ (F ∘ e'.symm) (e' (f x))) := by
    refine ⟨hF.continuousAt,?_⟩
    simpa only [writtenInExtChartAt,mfld_simps] using!
      (hfc.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt (s := range 𝓘(ℝ,E'))
  have hfi : Function.Injective (fderiv ℝ (F ∘ e'.symm) (e' (f x))) := by
    have hh := hi
    rw [hfd.mfderiv] at hh
    simpa only using! hh
  have hfe : ContinuousAt (f ∘ e.symm) y := by
    apply ContinuousAt.comp _ (e.symm.continuousAt hy)
    rwa [he]
  have hg : ContinuousAt g y := by
    have hh : ContinuousAt e' ((f ∘ e.symm) y) := by
      simpa only [Function.comp_apply,he] using e'.continuousAt he'
    exact hh.comp hfe
  have hfg : (F ∘ e'.symm) ∘ g =ᶠ[𝓝 y] (F ∘ f) ∘ e.symm := by
    have hh : ∀ᶠ z in 𝓝 y, f (e.symm z) ∈ e'.source :=
      hfe.eventually (by
        change e'.source ∈ 𝓝 ((f ∘ e.symm) y)
        simpa only [Function.comp_apply,he] using e'.open_source.mem_nhds he')
    filter_upwards [hh] with z hz
    exact congrArg F (e'.left_inv hz)
  have hsc : ContDiffAt ℝ ∞ ((F ∘ f) ∘ e.symm) y := by
    simpa only [mfld_simps,contDiffWithinAt_univ] using! (contMDiffAt_iff.mp hcomp).2
  have hgc : ContDiffAt ℝ ∞ g y := by
    apply contDiffAt_of_comp_immersion (f := F ∘ e'.symm)
    · simpa only [hgval] using hfc
    · simpa only [hgval] using hfi
    · exact hg
    · exact hsc.congr_of_eventuallyEq hfg
  apply contMDiffAt_iff.mpr
  refine ⟨hf,?_⟩
  simpa only [mfld_simps] using! hgc.contDiffWithinAt (s := range 𝓘(ℝ,E))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.contMDiffAt_of_comp_regular_map
