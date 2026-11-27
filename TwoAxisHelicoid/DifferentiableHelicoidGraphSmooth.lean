import TwoAxisHelicoid.DifferentiableGraphParameterSmooth
import TwoAxisHelicoid.HelicoidGraphSmoothness
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import TwoAxisHelicoid.HelicoidLocalGraph

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped ContDiff

/-- In a physical surface chart, a differentiable scalar normal graph is
smooth whenever it parametrizes a smooth immersion. All projection and
signed-distance derivatives are taken in the genuine helicoid tube. -/
theorem differentiable_helicoid_graph_height_smooth_at
    {Y : ℂ → HelicoidTubeCoordinates} {g : ℝ × ℝ → ℂ} {u : ℝ × ℝ → ℝ} {b : ℝ × ℝ}
    (smooth : ContDiffAt ℝ ∞ Y (g b)) (immersed : Function.Injective (fderiv ℝ Y (g b)))
    (param : ContinuousAt g b) (du : DifferentiableAt ℝ u b)
    (small : ∀ᶠ w in 𝓝 b, |u w|<1)
    (graph : ∀ᶠ w in 𝓝 b, Y (g w)=helicoidTubeMap ((u w,w.1),w.2)) :
    ContDiffAt ℝ ∞ u b := by
  let tube := fun w : ℝ × ℝ => ((u w,w.1),w.2)
  have tubeDiff : DifferentiableAt ℝ tube b := (du.prodMk differentiableAt_fst).prodMk differentiableAt_snd
  have dY : DifferentiableAt ℝ (Y ∘ g) b :=
    ((helicoidTubeMap_contDiff.differentiable (by simp)).differentiableAt.comp b tubeDiff).congr_of_eventuallyEq graph
  have target : Y (g b)∈helicoidTubeEquiv.target := by
    rw [graph.self_of_nhds]
    exact helicoidTubeEquiv.map_source (show tube b∈helicoidTubeEquiv.source from small.self_of_nhds)
  have inverse : (helicoidBaseCoordinates ∘ Y) ∘ g =ᶠ[𝓝 b] id := by
    filter_upwards [graph,small] with w hw close
    have original : helicoidTubeEquiv.symm (helicoidTubeMap ((u w,w.1),w.2)) = ((u w,w.1),w.2) :=
      helicoidTubeEquiv.left_inv close
    exact (congrArg helicoidBaseCoordinates hw).trans (by
      simp only [helicoidBaseCoordinates,original]
      rfl)
  have dim : Module.finrank ℝ ℂ=Module.finrank ℝ (ℝ × ℝ) := by
    simp [Module.finrank_prod,Complex.finrank_real_complex]
  have regular := differentiable_graph_parameter_is_smooth dim smooth immersed param dY
    (helicoidBaseCoordinates_contDiffAt target) inverse
  have distSmooth := (helicoidSignedDistance_contDiffAt target).comp b (smooth.comp b regular)
  apply distSmooth.congr_of_eventuallyEq
  filter_upwards [graph,small] with w hw close
  change u w=helicoidSignedDistance (Y (g w))
  rw [hw]
  have original : helicoidTubeEquiv.symm (helicoidTubeMap ((u w,w.1),w.2))=((u w,w.1),w.2) :=
    helicoidTubeEquiv.left_inv close
  exact (congrArg (fun y : HelicoidTubeCoordinates => y.1.1) original).symm

/-- Smoothness of the actual height on any open base, including its given
parametrization in an arbitrary surface chart. This requires only
differentiability of the height originally offered by the graph. -/
theorem differentiable_helicoid_normal_graph_is_smooth {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (Y : M → HelicoidTubeCoordinates)
    (regular : ∀ x : M, let e := chartAt ℂ x
      ContDiffAt ℝ ∞ (Y ∘ e.symm) (e x) ∧ Function.Injective (fderiv ℝ (Y ∘ e.symm) (e x)))
    {S : Set M} {B : Set (ℝ × ℝ)} (opened : IsOpen B)
    (E : S ≃ₜ B) (u : B → ℝ) (du : DifferentiableOn ℝ (extendOpenScalar u) B)
    (bounded : ∀ b, |u b|<1)
    (actual : ∀ b : B, Y (E.symm b).1=helicoidTubeMap ((u b,b.1.1),b.1.2)) :
    ContDiffOn ℝ ∞ (extendOpenScalar u) B := by
  classical
  intro b hb
  let x := (E.symm ⟨b,hb⟩).1
  let e := chartAt ℂ x
  let p := fun w : ℝ × ℝ => if hw : w∈B then (E.symm ⟨w,hw⟩).1 else x
  have p0 : p b=x := by simp [p,hb,x]
  have cpOn : ContinuousOn p B := continuousOn_iff_continuous_domRestrict.mpr (by
    have same : B.domRestrict p=(fun w : B => (E.symm w).1) := by
      funext w
      simp [Set.domRestrict,p,w.2]
    rw [same]
    exact continuous_subtype_val.comp E.symm.continuous)
  have cp := cpOn.continuousAt (opened.mem_nhds hb)
  have center : p b∈e.source := p0 ▸ mem_chart_source ℂ x
  let g := e ∘ p
  have cg : ContinuousAt g b := (e.continuousAt center).comp cp
  have charted := cp.eventually (e.open_source.mem_nhds center)
  have chartSmooth := regular x
  have atCenter : g b=e x := congrArg e p0
  have near : ∀ᶠ w in 𝓝 b, (Y ∘ e.symm) (g w)=
      helicoidTubeMap ((extendOpenScalar u w,w.1),w.2) := by
    filter_upwards [opened.mem_nhds hb,charted] with w hw chart
    change Y (e.symm (e (p w)))=_
    rw [e.left_inv chart]
    simpa only [p,dite_eq_left hw,extendOpenScalar] using actual ⟨w,hw⟩
  have small : ∀ᶠ w in 𝓝 b, |extendOpenScalar u w|<1 := by
    filter_upwards [opened.mem_nhds hb] with w hw
    simpa only [extendOpenScalar,dite_eq_left hw] using bounded ⟨w,hw⟩
  have sm := differentiable_helicoid_graph_height_smooth_at
    (Y:=Y ∘ e.symm) (g:=g) (u:=extendOpenScalar u) (b:=b)
    (atCenter.symm ▸ chartSmooth.1) (atCenter.symm ▸ chartSmooth.2) cg
    ((du b hb).differentiableAt (opened.mem_nhds hb)) small near
  exact sm.contDiffWithinAt

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.differentiable_helicoid_graph_height_smooth_at
#print axioms TwoAxisHelicoid.differentiable_helicoid_normal_graph_is_smooth
