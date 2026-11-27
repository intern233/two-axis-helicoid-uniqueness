import TwoAxisHelicoid.SigmaNormalization

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta

theorem thetaSigma_deriv_neg (t : ℝ) (z : ℂ) : deriv (thetaSigma t) (-z) = deriv (thetaSigma t) z := by
  have he : (fun w => thetaSigma t (-w)) = fun w => -thetaSigma t w := funext (thetaSigma_neg t)
  have h := iteratedDeriv_comp_neg 1 (thetaSigma t) z
  rw [he,iteratedDeriv_fun_neg] at h
  simpa using h.symm

theorem thetaSigma_second_neg (t : ℝ) (z : ℂ) :
    iteratedDeriv 2 (thetaSigma t) (-z) = -iteratedDeriv 2 (thetaSigma t) z := by
  have he : (fun w => thetaSigma t (-w)) = fun w => -thetaSigma t w := funext (thetaSigma_neg t)
  have h := iteratedDeriv_comp_neg 2 (thetaSigma t) z
  rw [he,iteratedDeriv_fun_neg] at h
  simpa using h.symm

theorem thetaSigma_second {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    iteratedDeriv 2 (thetaSigma t) z =
      (thetaZeta t z^2-(rhombicPeriodPair t ht0).weierstrassP z)*thetaSigma t z := by
  have he : deriv (thetaSigma t) =ᶠ[𝓝 z] fun w => thetaZeta t w*thetaSigma t w := by
    filter_upwards [(rhombicPeriodPair t ht0).isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact (thetaSigma_hasDerivAt_zeta ht ht0 hw).deriv
  have hd := (thetaZeta_hasDerivAt ht ht0 hz).mul (thetaSigma_hasDerivAt_zeta ht ht0 hz)
  have hd' := hd.congr_of_eventuallyEq he
  rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hd'.deriv]
  ring

theorem thetaSigma_wronskian {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    deriv (thetaSigma t) z^2-iteratedDeriv 2 (thetaSigma t) z*thetaSigma t z =
      (rhombicPeriodPair t ht0).weierstrassP z*thetaSigma t z^2 := by
  rw [(thetaSigma_hasDerivAt_zeta ht ht0 hz).deriv,thetaSigma_second ht ht0 hz]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_wronskian
