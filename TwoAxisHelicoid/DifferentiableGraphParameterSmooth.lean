module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace TwoAxisHelicoid
open Filter Topology
open scoped ContDiff

/-- In a regular smooth surface, a differentiable parametrized graph over
a smooth projection of the same dimension is a smooth parametrization.
The derivative of the projection is deduced from its actual section. -/
theorem differentiable_graph_parameter_is_smooth
    {B E F : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : E → F} {g : B → E} {proj : F → B} {b : B}
    (dims : Module.finrank ℝ E=Module.finrank ℝ B)
    (smoothX : ContDiffAt ℝ ∞ X (g b)) (imm : Function.Injective (fderiv ℝ X (g b)))
    (continuousG : ContinuousAt g b) (graph : DifferentiableAt ℝ (X ∘ g) b)
    (smoothProj : ContDiffAt ℝ ∞ proj (X (g b))) (sectionEq : (proj ∘ X) ∘ g =ᶠ[𝓝 b] id) :
    ContDiffAt ℝ ∞ g b := by
  obtain ⟨L,left⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional imm
  have dg : DifferentiableAt ℝ g b :=
    (HasFDerivAt.of_comp_of_leftInverse (f'symm := L) continuousG
      (smoothX.differentiableAt (by simp)).hasFDerivAt graph.hasFDerivAt .rfl left).differentiableAt
  let f := proj ∘ X
  have sf : ContDiffAt ℝ ∞ f (g b) := smoothProj.comp (g b) smoothX
  have composition := (sf.differentiableAt (by simp)).hasFDerivAt.comp b dg.hasFDerivAt
  have derivative : (fderiv ℝ f (g b)).comp (fderiv ℝ g b)=ContinuousLinearMap.id ℝ B :=
    composition.unique ((hasFDerivAt_id b).congr_of_eventuallyEq sectionEq)
  have onto : Function.Surjective (fderiv ℝ f (g b)) := fun v =>
    ⟨fderiv ℝ g b v,congrArg (fun T : B →L[ℝ] B => T v) derivative⟩
  have oneToOne : Function.Injective (fderiv ℝ f (g b)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dims
      (f:=(fderiv ℝ f (g b)).toLinearMap)).mpr onto
  let df : E ≃L[ℝ] B :=
    (LinearEquiv.ofBijective (fderiv ℝ f (g b)).toLinearMap ⟨oneToOne,onto⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt f (df : E →L[ℝ] B) (g b) := by
    have same : (df : E →L[ℝ] B) = fderiv ℝ f (g b) := by ext v; rfl
    rw [same]
    exact (sf.differentiableAt (by simp)).hasFDerivAt
  let e := sf.toOpenPartialHomeomorph f hd (by simp)
  have source : g b ∈ e.source := sf.mem_toOpenPartialHomeomorph_source hd (by simp)
  have invSmooth : ContDiffAt ℝ ∞ e.symm (f (g b)) := sf.to_localInverse hd (by simp)
  have sectionSmooth : ContDiffAt ℝ ∞ (f ∘ g) b := contDiffAt_id.congr_of_eventuallyEq sectionEq
  apply (invSmooth.comp b sectionSmooth).congr_of_eventuallyEq
  filter_upwards [continuousG.eventually (e.open_source.mem_nhds source)] with y hy
  exact (e.left_inv hy).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.differentiable_graph_parameter_is_smooth
