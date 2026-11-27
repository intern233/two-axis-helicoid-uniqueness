import TwoAxisHelicoid.BernsteinBreinerConformalFilling
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace TwoAxisHelicoid
open Complex Set Filter TopologicalSpace
open scoped Topology ContDiff Manifold

/-- The inclusion of an open complex submanifold is locally
biholomorphic in its inherited atlas. -/
theorem open_complex_subdomain_local_biholomorphism {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N]
    (U : Opens N) : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (Subtype.val : U → N) := by
  intro p
  let _ : Nonempty U := ⟨p⟩
  let e := U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → N)
  have inv : ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm e.target := by
    intro z hz
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff e.symm e.target z).mp
    apply contMDiffWithinAt_id.congr
    · intro w hw
      exact e.right_inv hw
    · exact e.right_inv hz
  let D : PartialDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) U N ω :=
    { toPartialEquiv := e.toPartialEquiv, open_source := e.open_source, open_target := e.open_target,
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn, contMDiffOn_invFun := inv }
  exact ⟨D,Set.mem_univ p,fun _ _ => rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.open_complex_subdomain_local_biholomorphism
