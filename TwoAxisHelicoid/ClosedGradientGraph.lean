import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set
open scoped NNReal

/-- Poincaré's estimate makes the projection of the closed Dirichlet graph
onto the gradient space a closed embedding. Every gradient in the closure
has a unique scalar potential in that same graph. -/
theorem lift_from_closed_gradient_graph {F E : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : Submodule ℝ (F × E)) {D : ℝ} (bound : ∀ x∈G, ‖x.1‖ ≤ D*‖x.2‖)
    {e : E} (approx : e∈(G.map (LinearMap.snd ℝ F E)).topologicalClosure) :
    ∃! v : F, (v,e)∈G.topologicalClosure := by
  let H := G.topologicalClosure
  let : CompleteSpace H := G.isClosed_topologicalClosure.completeSpace_coe
  let f : H →L[ℝ] E := (ContinuousLinearMap.snd ℝ F E).comp H.subtypeL
  have est (x : H) : ‖x.val.1‖≤D*‖x.val.2‖ :=
    closure_minimal bound (isClosed_le continuous_fst.norm (continuous_const.mul continuous_snd.norm)) x.2
  let k : ℝ≥0 := ⟨max 1 D,le_trans zero_le_one (le_max_left _ _)⟩
  have inv : AntilipschitzWith k f := by
    apply AddMonoidHomClass.antilipschitz_of_bound
    intro x
    change max ‖x.val.1‖ ‖x.val.2‖≤max 1 D * ‖x.val.2‖
    apply max_le
    · exact (est x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 D) (norm_nonneg x.val.2)
  have contains : G.map (LinearMap.snd ℝ F E) ≤ f.range := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨x,G.le_topologicalClosure hx⟩,rfl⟩
  have rangeClosed : IsClosed (f.range : Set E) := inv.isClosed_range f.uniformContinuous
  obtain ⟨x,hx⟩ := (Submodule.topologicalClosure_minimal _ contains rangeClosed) approx
  change x.val.2=e at hx
  refine ⟨x.val.1,?_,?_⟩
  · rw [←hx]
    exact x.2
  · intro w hw
    have id : (⟨(w,e),hw⟩:H)=x := inv.injective (show f ⟨(w,e),hw⟩=f x from hx.symm)
    exact congrArg (fun y : H => y.val.1) id
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lift_from_closed_gradient_graph
