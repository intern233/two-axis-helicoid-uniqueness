import TwoAxisHelicoid.ManifoldImmersionTest

namespace TwoAxisHelicoid
open Filter Topology
open scoped ContDiff Manifold

variable {M E E' A : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [ChartedSpace E M] [ChartedSpace E' M]

/-- Two surface structures with the same actual regular ambient map
are mutually smooth at that point. -/
theorem common_immersion_structures_compatible {F : M → A} {x : M}
    (hF : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ F x)
    (hi : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) F x))
    (hF' : ContMDiffAt 𝓘(ℝ,E') 𝓘(ℝ,A) ∞ F x)
    (hi' : Function.Injective (mfderiv 𝓘(ℝ,E') 𝓘(ℝ,A) F x)) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ (@id M) x ∧
      ContMDiffAt 𝓘(ℝ,E') 𝓘(ℝ,E) ∞ (@id M) x := by
  constructor
  · exact contMDiffAt_of_comp_regular_map hF' hi' continuousAt_id hF
  · exact contMDiffAt_of_comp_regular_map hF hi continuousAt_id hF'

/-- If a cap fixes an open neighborhood of the compact core, its
constructed smooth structure agrees there with the original one.
This is a smooth identification, rather than just a common topology. -/
theorem locally_fixed_cap_structures_compatible {F X : M → A} {x : M}
    (heq : F =ᶠ[𝓝 x] X)
    (hX : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ X x)
    (hXi : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) X x))
    (hF : ContMDiffAt 𝓘(ℝ,E') 𝓘(ℝ,A) ∞ F x)
    (hFi : Function.Injective (mfderiv 𝓘(ℝ,E') 𝓘(ℝ,A) F x)) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ (@id M) x ∧
      ContMDiffAt 𝓘(ℝ,E') 𝓘(ℝ,E) ∞ (@id M) x := by
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ F x := hX.congr_of_eventuallyEq heq
  have hci : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) F x) := by
    rw [heq.mfderiv_eq]
    exact (tangentSpaceCast 𝓘(ℝ,A) (X x) (F x)).injective.comp hXi
  exact common_immersion_structures_compatible hc hci hF hFi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.common_immersion_structures_compatible
#print axioms TwoAxisHelicoid.locally_fixed_cap_structures_compatible
