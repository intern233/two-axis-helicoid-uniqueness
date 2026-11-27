import TwoAxisHelicoid.ThetaLogPeriodicity
import TwoAxisHelicoid.LogSecondCancellation

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaScaledJet thetaLogSecond

noncomputable def thetaWeierstrassDifference (t : ℝ) (ht : 0 < t) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ (rhombicPeriodPair t ht).lattice then 0
  else thetaLogSecond t z-(rhombicPeriodPair t ht).weierstrassP z-thetaEtaExpression t

theorem thetaScaledJet_zero_iff_lattice {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (z : ℂ) :
    thetaScaledJet t 0 z = 0 ↔ z ∈ (rhombicPeriodPair t ht0).lattice := by
  simp only [thetaScaledJet,pow_zero,one_mul]
  rw [show (Real.pi/2:ℂ)*z = Real.pi*z/2 by ring]
  exact thetaJet_zero_iff_rhombic_lattice ht z

theorem thetaLogSecond_meromorphic {t : ℝ} (ht : 0 < t) : Meromorphic (thetaLogSecond t) := by
  have he : thetaLogSecond t = fun z =>
      (thetaScaledJet t 1 z/thetaScaledJet t 0 z)^2-thetaScaledJet t 2 z/thetaScaledJet t 0 z :=
    funext (thetaLogSecond_scaled t)
  rw [he]
  intro z
  have h0 := (thetaScaledJet_analyticAt ht 0 z).meromorphicAt
  have h1 := (thetaScaledJet_analyticAt ht 1 z).meromorphicAt
  have h2 := (thetaScaledJet_analyticAt ht 2 z).meromorphicAt
  exact ((h1.div h0).pow 2).sub (h2.div h0)

theorem thetaLogSecond_analyticAt {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) : AnalyticAt ℂ (thetaLogSecond t) z := by
  have hn : thetaScaledJet t 0 z ≠ 0 := mt (thetaScaledJet_zero_iff_lattice ht ht0 z).mp hz
  have he : thetaLogSecond t = fun z =>
      (thetaScaledJet t 1 z/thetaScaledJet t 0 z)^2-thetaScaledJet t 2 z/thetaScaledJet t 0 z :=
    funext (thetaLogSecond_scaled t)
  rw [he]
  have h0 := thetaScaledJet_analyticAt ht0 0 z
  have h1 := thetaScaledJet_analyticAt ht0 1 z
  have h2 := thetaScaledJet_analyticAt ht0 2 z
  exact ((h1.div h0 hn).pow 2).sub (h2.div h0 hn)

theorem thetaWeierstrassDifference_meromorphic {t : ℝ} (ht : 0 < t) :
    Meromorphic (thetaWeierstrassDifference t ht) := by
  let L := rhombicPeriodPair t ht
  have hf : Meromorphic (fun z => thetaLogSecond t z-L.weierstrassP z-thetaEtaExpression t) := by
    intro z
    exact (((thetaLogSecond_meromorphic ht z).sub (L.meromorphic_weierstrassP z)).sub
      analyticAt_const.meromorphicAt)
  intro z
  refine (hf z).congr ?_
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds z)] with w hw hw'
  rw [thetaWeierstrassDifference,ite_eq_right (by simp_all [L])]

theorem thetaWeierstrassDifference_zero (t : ℝ) (ht : 0 < t) :
    thetaWeierstrassDifference t ht 0 = 0 := by
  simp [thetaWeierstrassDifference]

theorem thetaWeierstrassDifference_weighted {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) :
    (thetaWeierstrassDifference t ht0*(thetaScaledJet t 0)^2*(id : ℂ → ℂ)^2) =ᶠ[𝓝 0]
      logSecondNumerator (thetaScaledJet t) ((rhombicPeriodPair t ht0).weierstrassPExcept 0)
        (thetaEtaExpression t) := by
  let L := rhombicPeriodPair t ht0
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases hz0 : z = 0
  · simp [hz0,logSecondNumerator,thetaScaledJet_zero_at_zero]
  have hzL : z ∉ L.lattice := by simpa [hz0] using hz
  change z ∉ (rhombicPeriodPair t ht0).lattice at hzL
  have hf0 : thetaScaledJet t 0 z ≠ 0 := mt (thetaScaledJet_zero_iff_lattice ht ht0 z).mp hzL
  have hp : L.weierstrassP z = L.weierstrassPExcept 0 z+1/z^2 := by
    simpa using (L.weierstrassPExcept_add (0 : L.lattice) z).symm
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq,thetaWeierstrassDifference,
    ite_eq_right hzL,thetaLogSecond_scaled,logSecondNumerator]
  change (((thetaScaledJet t 1 z/thetaScaledJet t 0 z)^2-
      thetaScaledJet t 2 z/thetaScaledJet t 0 z)-L.weierstrassP z-thetaEtaExpression t)*
      (thetaScaledJet t 0 z)^2*z^2 = _
  rw [hp]
  field_simp
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaWeierstrassDifference_weighted
