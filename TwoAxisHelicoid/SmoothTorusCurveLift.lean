import TwoAxisHelicoid.TorusActualLifts
import TwoAxisHelicoid.PeriodTorusComplexManifold
import TwoAxisHelicoid.PiecewiseComplexPeriods
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology Manifold ContDiff

/-- An ordinary C¹ curve in the actual torus lifts through its universal
cover as an ordinary C¹ plane curve with any prescribed initial value. -/
theorem smooth_torus_curve_has_plane_lift (L : PeriodPair) (g : ℝ → PeriodTorus L)
    (hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 g) (z : ℂ) (hz : periodTorusProjection L z = g 0) :
    ∃ F : ℝ → ℂ, ContDiff ℝ 1 F ∧ F 0 = z ∧ ∀ s, periodTorusProjection L (F s) = g s := by
  let G : C(ℝ,PeriodTorus L) := ⟨g,hg.continuous⟩
  obtain ⟨F,⟨hF0,hF⟩,_⟩ := (periodTorusProjection_isCoveringMap L).existsUnique_continuousMap_lifts G 0 z hz
  have proj (s : ℝ) : periodTorusProjection L (F s) = g s := congrFun hF s
  refine ⟨F,contDiff_iff_contDiffAt.mpr (fun s => ?_),hF0,proj⟩
  let e := chartAt ℂ (g s)
  let p : ℝ → ℂ := fun u => e (g u)
  have hpc : ContDiffAt ℝ 1 p s := (contMDiffAt_iff_target.mp (hg s)).2.contDiffAt
  have hnh : ∀ᶠ u in 𝓝 s, g u ∈ e.source := hg.continuous.continuousAt (e.open_source.mem_nhds (mem_chart_source ℂ (g s)))
  have hl : ∀ᶠ u in 𝓝 s, F u-p u ∈ L.lattice := by
    filter_upwards [hnh] with u hu
    apply (periodTorusProjection_eq_iff L (p u) (F u)).mp
    rw [proj,← periodTorus_chart_symm_eq_projection L (g s)]
    exact e.left_inv hu
  have hd : IsDiscrete (L.lattice : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology L.lattice))
  have ht : Tendsto (fun u => F u-p u) (𝓝 s) (𝓝[L.lattice] (F s-p s)) :=
    tendsto_nhdsWithin_iff.mpr ⟨F.continuous.continuousAt.sub hpc.continuousAt,hl⟩
  rw [hd.nhdsWithin _ hl.self_of_nhds] at ht
  apply (hpc.add (contDiffAt_const (c := F s-p s))).congr_of_eventuallyEq
  filter_upwards [tendsto_pure.mp ht] with u hu
  change F u = p u+(F s-p s)
  linear_combination hu

/-- A smooth non-puncture-hitting quotient loop has an actual piecewise
period arc over its entire unit parametrization. -/
theorem smooth_torus_curve_has_period_arc (L : PeriodPair) (g : ℝ → PeriodTorus L)
    (hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 g) (z : ℂ) (hz : periodTorusProjection L z = g 0)
    (hp : ∀ s ∈ Icc (0:ℝ) 1, g s ≠ 0) :
    ∃ A : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ, A.left = 0 ∧ A.right = 1 ∧
      A.curve 0 = z ∧ ∀ s, periodTorusProjection L (A.curve s) = g s := by
  obtain ⟨F,hF,hF0,hG⟩ := smooth_torus_curve_has_plane_lift L g hg z hz
  let A : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ := {
    left := 0
    right := 1
    ordered := zero_le_one
    curve := F
    velocity := deriv F
    stays := fun s hs hm => hp s hs ((hG s).symm.trans ((periodTorusProjection_eq_zero L _).mpr hm))
    continuous_curve := hF.continuous.continuousOn
    continuous_velocity := hF.continuous_deriv_one.continuousOn
    derivative := fun s _ => (hF.differentiable one_ne_zero s).hasDerivAt }
  exact ⟨A,rfl,rfl,hF0,hG⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_torus_curve_has_period_arc
