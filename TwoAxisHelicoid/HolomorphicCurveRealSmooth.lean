import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace TwoAxisHelicoid
open scoped Topology ContDiff Manifold
/-- Holomorphic maps of complex curves are smooth maps on their underlying
real surfaces, in the same topological charts. -/
theorem holomorphic_curve_map_real_smooth {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N] {f : M → N}
    (h : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f := by
  intro x
  obtain ⟨hc,hd⟩ := contMDiffAt_iff.mp (h x)
  refine contMDiffAt_iff.mpr ⟨hc,?_⟩
  simpa only [mfld_simps] using! (hd.restrict_scalars ℝ).of_le (show (∞ : WithTop ℕ∞) ≤ ω by simp)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.holomorphic_curve_map_real_smooth
