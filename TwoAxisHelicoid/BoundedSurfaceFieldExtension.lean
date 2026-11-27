import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped ContDiff Manifold

/-- Local extensions of a field on a closed surface glue to an ambient
field with the same convex velocity constraint, including off the surface. -/
theorem bounded_surface_field_extension {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set E} (hS : IsClosed S)
    {C : Set F} (hC : Convex ℝ C) (hzero : (0:F) ∈ C) (v : E → F)
    (localExt : ∀ x ∈ S, ∃ U ∈ 𝓝 x, ∃ g : E → F, ContDiffOn ℝ 1 g U ∧
      ∀ y ∈ U, g y ∈ C ∧ (y ∈ S → g y = v y)) :
    ∃ V : E → F, ContDiff ℝ 1 V ∧ (∀ x, V x ∈ C) ∧ EqOn V v S := by
  classical
  let T := fun x => {w : F | w ∈ C ∧ (x ∈ S → w = v x)}
  have cv (x) : Convex ℝ (T x) := by
    by_cases hx : x ∈ S
    · have e : T x = C ∩ {v x} := by ext w; simp [T,hx]
      rw [e]
      exact hC.inter (convex_singleton _)
    · simpa [T,hx] using hC
  obtain ⟨V,hV⟩ := exists_contMDiffMap_forall_mem_convex_of_local (𝓘(ℝ,E)) cv (n := 1) (by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U,hu,g,hg,hm⟩ := localExt x hx
      exact ⟨U,hu,g,hg.contMDiffOn,hm⟩
    · exact ⟨Sᶜ,hS.isOpen_compl.mem_nhds hx,fun _ => 0,contMDiffOn_const,
        fun _ hy => ⟨hzero,fun hn => (hy hn).elim⟩⟩)
  exact ⟨V,V.contMDiff.contDiff,fun x => (hV x).1,fun x hx => (hV x).2 hx⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_surface_field_extension
