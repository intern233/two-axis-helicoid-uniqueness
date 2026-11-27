import TwoAxisHelicoid.LogSecondCancellation

namespace TwoAxisHelicoid
set_option maxHeartbeats 1000000
open Complex

attribute [local fun_prop] AnalyticAt.contDiffAt in
theorem logSecondNumerator_sixth
    (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (c : ℂ)
    (hF : ∀ j, AnalyticAt ℂ (F j) 0) (hg : AnalyticAt ℂ g 0)
    (hD : ∀ j n, iteratedDeriv n (F j) 0 = F (j+n) 0)
    (h0 : F 0 0 = 0) (h2 : F 2 0 = 0) (hg0 : g 0 = 0) :
    iteratedDeriv 6 (logSecondNumerator F g c) 0 =
      40*(F 3 0)^2-72*F 1 0*F 5 0-240*c*F 1 0*F 3 0-
        360*iteratedDeriv 2 g 0*(F 1 0)^2 := by
  have hf0 := hF 0
  have hf1 := hF 1
  have hf2 := hF 2
  unfold logSecondNumerator
  simp_rw [pow_two]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_sub,iteratedDeriv_fun_mul,
    iteratedDeriv_fun_add,iteratedDeriv_const,iteratedDeriv_fun_id_zero,hD]
  norm_num [Finset.sum_range_succ,Nat.choose,h0,h2,hg0]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.logSecondNumerator_sixth
