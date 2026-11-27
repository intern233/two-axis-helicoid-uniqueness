import TwoAxisHelicoid.VerticalBranchAnalytic
import TwoAxisHelicoid.VerticalBranchLimit

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

/-- Proposition 5.1 for the actual normalized elliptic functions. The
geometric reduction from an arbitrary minimal surface is a separate theorem. -/
theorem actual_vertical_domain_theorem :
    StrictMonoOn ellipticFReal (Ioi (0:ℝ)) ∧
    (∃! t : ℝ, 0 < t ∧ ellipticFReal t = 0) ∧
    ((70945978/100000000:ℝ) < ellipticCriticalT ∧ ellipticCriticalT < 70945980/100000000) ∧
    (100000000/70945980 < ellipticVerticalUpper ∧ ellipticVerticalUpper < 100000000/70945978) ∧
    (∀ t : ℝ, 0 < t → ((∃! a : ℝ, a ∈ Ioo (0:ℝ) 1 ∧ thetaG t a = 0) ↔ t < ellipticVerticalUpper)) ∧
    (∀ t ∈ Ioo (0:ℝ) ellipticVerticalUpper, verticalA t ∈ Ioo (0:ℝ) 1 ∧ thetaG t (verticalA t) = 0) ∧
    AnalyticOnNhd ℝ verticalA (Ioo (0:ℝ) ellipticVerticalUpper) ∧
    Tendsto verticalA (𝓝[<] ellipticVerticalUpper) (𝓝 1) :=
  ⟨ellipticFReal_strictMono_of_pos,existsUnique_ellipticFReal_root,ellipticCriticalT_location,
    ellipticVerticalUpper_location,fun _ ht => existsUnique_thetaG_zero_full_domain ht,
    fun _ ht => verticalA_spec ht,verticalA_analyticOnNhd,verticalA_tendsto_one⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_vertical_domain_theorem
