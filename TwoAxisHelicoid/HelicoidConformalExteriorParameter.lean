import TwoAxisHelicoid.HelicoidGraphConformalMetric
import TwoAxisHelicoid.HelicoidEndDomain
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

namespace TwoAxisHelicoid
open Complex Real Set Filter Bornology
open scoped Topology

noncomputable def helicoidConformalBaseHomeomorph : ℂ ≃ₜ ℝ × ℝ :=
  Complex.equivRealProdCLM.toHomeomorph.trans (Real.sinhHomeomorph.prodCongr (Homeomorph.refl ℝ))

theorem helicoidConformalBaseHomeomorph_apply (z : ℂ) :
    helicoidConformalBaseHomeomorph z=helicoidConformalBase z := rfl

theorem helicoidConformalBase_proper :
    Tendsto helicoidConformalBase (cobounded ℂ) (cobounded (ℝ × ℝ)) := by
  rw [Metric.cobounded_eq_cocompact,Metric.cobounded_eq_cocompact]
  exact helicoidConformalBaseHomeomorph.isClosedEmbedding.tendsto_cocompact

theorem helicoidConformalBase_inv_differentiable (q : ℝ × ℝ) :
    DifferentiableAt ℝ helicoidConformalBaseHomeomorph.symm q := by
  exact Complex.equivRealProdCLM.symm.differentiableAt.comp q
    (((Real.differentiable_arsinh _).comp q differentiableAt_fst).prodMk differentiableAt_snd)

/-- The actual smooth tube foot recovers the complex conformal parameter
on a small normal graph, with no choice of inverse branch. -/
noncomputable def helicoidProjectedComplexParameter (y : HelicoidTubeCoordinates) : ℂ :=
  helicoidConformalBaseHomeomorph.symm (helicoidBaseCoordinates y)

theorem helicoidProjectedComplexParameter_differentiable {y : HelicoidTubeCoordinates}
    (hy : y∈helicoidTubeEquiv.target) : DifferentiableAt ℝ helicoidProjectedComplexParameter y :=
  (helicoidConformalBase_inv_differentiable _).comp y ((helicoidBaseCoordinates_contDiffAt hy).differentiableAt (by simp))

theorem helicoidProjectedComplexParameter_graph {u : ℝ × ℝ → ℝ} {z : ℂ}
    (small : |u (helicoidConformalBase z)| < 1) :
    helicoidGraphMap u (helicoidConformalBase z)∈helicoidTubeEquiv.target ∧
    helicoidProjectedComplexParameter (helicoidGraphMap u (helicoidConformalBase z))=z := by
  let q := helicoidConformalBase z
  have src : ((u q,q.1),q.2)∈helicoidTubeEquiv.source := small
  refine ⟨helicoidTubeEquiv.map_source src,?_⟩
  have b : helicoidBaseCoordinates (helicoidGraphMap u q)=q := by
    change ((helicoidTubeEquiv.symm (helicoidTubeEquiv ((u q,q.1),q.2))).1.2,
      (helicoidTubeEquiv.symm (helicoidTubeEquiv ((u q,q.1),q.2))).2)=q
    rw [helicoidTubeEquiv.left_inv src]
  change helicoidConformalBaseHomeomorph.symm (helicoidBaseCoordinates (helicoidGraphMap u q))=z
  rw [b]
  exact helicoidConformalBaseHomeomorph.symm_apply_apply z

/-- Bounded graph height makes spatial escape imply escape of the actual
conformal parameter, even when the graph height has no interior extension
with controlled values. -/
theorem bounded_helicoid_graph_escape {α : Type*} {l : Filter α}
    {Z : α → ℂ} {s : α → ℝ} {Y : α → HelicoidTubeCoordinates}
    (graph : ∀ᶠ x in l, |s x|≤1 ∧ Y x=helicoidTubeMap ((s x,Real.sinh (Z x).re),(Z x).im))
    (escape : Tendsto (fun x => ‖Y x‖) l atTop) : Tendsto (fun x => ‖Z x‖) l atTop := by
  apply tendsto_atTop.mpr
  intro A
  let f := fun q : ℝ × ℂ => helicoidTubeMap ((q.1,Real.sinh q.2.re),q.2.im)
  have cont : Continuous f := helicoidTubeMap_contDiff.continuous.comp (by fun_prop)
  obtain ⟨B,bound⟩ := ((isCompact_Icc (a := (-1:ℝ)) (b := 1)).prod
    (isCompact_closedBall (0:ℂ) A) |>.image cont).isBounded.exists_norm_le
  filter_upwards [graph,escape.eventually_gt_atTop B] with x hx hB
  by_contra hn
  have inBall : Z x∈Metric.closedBall (0:ℂ) A := by simpa using (le_of_not_ge hn)
  have hb := bound (f (s x,Z x)) ⟨(s x,Z x),⟨abs_le.mp hx.1,inBall⟩,rfl⟩
  rw [hx.2] at hB
  exact (not_lt_of_ge hb) hB

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidConformalBase_proper
#print axioms TwoAxisHelicoid.helicoidProjectedComplexParameter_graph
#print axioms TwoAxisHelicoid.bounded_helicoid_graph_escape
