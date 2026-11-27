import TwoAxisHelicoid.ComplexEndCompactification
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology Function
open scoped Topology Manifold ContDiff

/-- A bump around a specified point with support in the image of the
closed coordinate disk. Its smoothness holds in every analytic chart,
including charts that cross the boundary of the distinguished chart. -/
theorem complex_curve_puncture_cutoff {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {d : OpenPartialHomeomorph M ℂ} (hd : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {P : M} (hp : P∈d.source) (center : d P=0)
    {R : ℝ} (pos : 0<R) (inside : closedBall (0:ℂ) R⊆d.target) :
    ∃ ρ : M → ℝ, ρ =ᶠ[𝓝 P] 1 ∧
      (∀ x∉d.symm '' closedBall (0:ℂ) R, ρ =ᶠ[𝓝 x] 0) ∧
      ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target,
        ContDiffAt ℝ 1 (fun w => ρ (e.symm w)) z := by
  classical
  let b : ContDiffBump (0:ℂ) := ⟨R/2,R,by positivity,by linarith⟩
  let K := d.symm '' closedBall (0:ℂ) R
  let ρ := d.source.indicator (fun x => b (d x))
  have ck : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (d.continuousOn_symm.mono inside)
  have sub : K⊆d.source := by
    rintro _ ⟨z,hz,rfl⟩
    exact d.map_target (inside hz)
  have agree (x : M) (hx : x∈d.source) : ρ =ᶠ[𝓝 x] fun y => b (d y) := by
    filter_upwards [d.open_source.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  have zero (x : M) (hx : x∉K) : ρ =ᶠ[𝓝 x] 0 := by
    filter_upwards [ck.isClosed.isOpen_compl.mem_nhds hx] with y hy
    by_cases dy : y∈d.source
    · rw [show ρ y=b (d y) from indicator_of_mem dy _]
      have loc : d y∉closedBall (0:ℂ) R := fun h => hy ⟨d y,h,d.left_inv dy⟩
      exact b.zero_of_le_dist (le_of_lt (lt_of_not_ge loc))
    · exact indicator_of_notMem dy _
  have cent : Tendsto d (𝓝 P) (𝓝 (0:ℂ)) := center ▸ (d.continuousAt hp)
  refine ⟨ρ,(agree P hp).trans (b.eventuallyEq_one.comp_tendsto cent),zero,?_⟩
  intro e he z hz
  by_cases loc : e.symm z∈K
  · have ds := sub loc
    have u := complexAtlas_realized_transition he hd (show z∈(e.symm.trans d).source from ⟨hz,ds⟩)
    have sm : ContDiffAt ℝ 1 (fun w => b ((e.symm.trans d) w)) z :=
      b.contDiffAt.comp z ((u.restrict_scalars ℝ).of_le (by simp))
    exact sm.congr_of_eventuallyEq ((agree _ ds).comp_tendsto (e.continuousAt_symm hz))
  · exact (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq ((zero _ loc).comp_tendsto (e.continuousAt_symm hz))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_curve_puncture_cutoff
