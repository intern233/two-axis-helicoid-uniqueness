import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace TwoAxisHelicoid
open Set Topology
open scoped ContDiff Manifold

/-- Smooth ambient extensions of relative germs on a closed set glue to a
single smooth function. The equality on the closed set is exact. -/
theorem smooth_extension_from_closed_germs {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set E) (hK : IsClosed K) (f : E → V)
    (h : ∀ x ∈ K, ∃ (U : Set E) (g : E → V), IsOpen U ∧ x ∈ U ∧
      ContDiffOn ℝ ∞ g U ∧ EqOn g f (U ∩ K)) :
    ∃ G : E → V, ContDiff ℝ ∞ G ∧ EqOn G f K := by
  classical
  let t (x : E) : Set V := if x ∈ K then {f x} else univ
  have ht (x : E) : Convex ℝ (t x) := by
    by_cases hx : x ∈ K
    · simp [t,hx]
    · rw [show t x = univ from ite_eq_right hx]
      exact convex_univ
  obtain ⟨G,hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ,E) (t := t) ht (n := (⊤ : ℕ∞)) (by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨U,g,hU,hxU,hg,he⟩ := h x hx
      refine ⟨U,hU.mem_nhds hxU,g,hg.contMDiffOn,fun y hy => ?_⟩
      by_cases hyK : y ∈ K
      · simpa [t,hyK] using he ⟨hy,hyK⟩
      · simp [t,hyK]
    · refine ⟨Kᶜ,hK.isOpen_compl.mem_nhds hx,fun _ => 0,contMDiffOn_const,fun y hy => ?_⟩
      have outside : y∉K := hy
      simp [t,outside])
  refine ⟨G,G.contMDiff.contDiff,fun x hx => ?_⟩
  simpa [t,hx] using hG x

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_extension_from_closed_germs
