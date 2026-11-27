import TwoAxisHelicoid.PhysicalDifferentialHeightGerm
import TwoAxisHelicoid.VanishingCircleDoublePole

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology MeasureTheory
open scoped Topology

/-- Recover the physical height coordinate and exponential Gauss map
from the meromorphic height coefficient in the original cap chart.
Zero peripheral periods remove its residue. -/
theorem original_cap_differentials_give_height_normal_form {x : ℂ → ℝ} {h g Q : ℂ → ℂ}
    (mer : MeromorphicAt h 0) (height : meromorphicOrderAt h 0=(-2:ℤ))
    (period : ∀ R : ℝ, 0<R → ∃ r∈Ioo (0:ℝ) R, (∮ z in C(0,r), h z)=0)
    (reg : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ x w ∧ scalarComplexCoefficient x w=h w)
    (order : meromorphicOrderAt (logDeriv g) 0=(-2:ℤ)) {α : ℝ} (qa : AnalyticAt ℂ Q 0)
    (gauss : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g w ∧ g w≠0 ∧ logDeriv g w-I*(α:ℂ)*h w=Q w) :
    α≠0 ∧ ∃ (H k F : ℂ → ℂ) (b : ℝ), AnalyticAt ℂ k 0 ∧ k 0=0 ∧ AnalyticAt ℂ F 0 ∧ F 0=0 ∧
      (∀ᶠ w in 𝓝[≠] (0:ℂ), HasDerivAt H (h w) w ∧ k (H w)⁻¹=w ∧ x w=b+(H w).re) ∧
      Tendsto (fun ξ : ℂ => k ξ⁻¹) (cobounded ℂ) (𝓝[≠] 0) ∧
      ∀ᶠ ξ in cobounded ℂ, H (k ξ⁻¹)=ξ ∧ x (k ξ⁻¹)=b+ξ.re ∧ g (k ξ⁻¹)=exp (I*(α:ℂ)*ξ+F ξ⁻¹) := by
  obtain ⟨a,P,nz,pa,part⟩ := double_pole_principal_part_of_zero_circle_periods mer height period
  exact cap_height_log_differentials_normalize_physical_end nz pa qa reg part order gauss

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_cap_differentials_give_height_normal_form
