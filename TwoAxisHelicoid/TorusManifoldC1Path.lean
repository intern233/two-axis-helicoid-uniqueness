import TwoAxisHelicoid.PuncturedTorusPathLift
import TwoAxisHelicoid.ActualTorusManifoldImmersion
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology Manifold ContDiff

/-- Standard manifold continuous differentiability on the interval implies
continuous differentiability in the natural quotient charts used to lift
the path. -/
theorem torusPathC1_of_contMDiffOn {L : PeriodPair} {q r : PuncturedPeriodTorus L} (γ : Path q r)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, ℂ) 1 γ.extend (Icc (0:ℝ) 1)) : TorusPathC1 γ := by
  let Y := fun t : ℝ => (γ.extend t).1
  have hval : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) :=
    contMDiff_subtype_val (U := puncturedPeriodTorusOpen L)
  have hY (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ContMDiffWithinAt 𝓘(ℝ) 𝓘(ℝ, ℂ) 1 Y (Icc 0 1) s :=
    hval.contMDiffAt.comp_contMDiffWithinAt s (hγ s hs)
  intro s hs
  let e := chartAt ℂ (Y s)
  let g := (extChartAt 𝓘(ℝ, ℂ) (Y s)) ∘ Y
  have hg : ContMDiffWithinAt 𝓘(ℝ) 𝓘(ℝ, ℂ) 1 g (Icc 0 1) s :=
    contMDiffAt_extChartAt.comp_contMDiffWithinAt s (hY s hs)
  refine ⟨g,contMDiffWithinAt_iff_contDiffWithinAt.mp hg,?_⟩
  have hc : Continuous Y := continuous_subtype_val.comp γ.continuous_extend
  have he : ∀ᶠ t in 𝓝 s, Y t ∈ e.source :=
    hc.continuousAt.eventually (e.open_source.mem_nhds (mem_chart_source ℂ (Y s)))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
  change periodTorusProjection L (e (Y t)) = Y t
  rw [← periodTorus_chart_symm_eq_projection L (Y s)]
  exact e.left_inv ht

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torusPathC1_of_contMDiffOn
