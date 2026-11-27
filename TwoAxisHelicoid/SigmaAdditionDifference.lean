import TwoAxisHelicoid.SigmaRatioPeriods
import TwoAxisHelicoid.SigmaSecondDerivative
import TwoAxisHelicoid.SigmaAdditionCancellation

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma

noncomputable def sigmaAdditionDifference (t : ℝ) (ht : 0 < t) (a z : ℂ) : ℂ := by
  classical
  exact if z ∈ (rhombicPeriodPair t ht).lattice then 0 else
    sigmaRatio (thetaSigma t) a z+(rhombicPeriodPair t ht).weierstrassP z-
      (rhombicPeriodPair t ht).weierstrassP a

theorem thetaSigmaRatio_meromorphic {t : ℝ} (ht : 0 < t) (a : ℂ) :
    Meromorphic (sigmaRatio (thetaSigma t) a) := by
  intro z
  unfold sigmaRatio
  have hu := (thetaSigma_analyticAt ht (z-a)).comp (f := fun w => w-a) (by fun_prop)
  have hv := (thetaSigma_analyticAt ht (z+a)).comp (f := fun w => w+a) (by fun_prop)
  exact (hu.meromorphicAt.mul hv.meromorphicAt).div
    (((thetaSigma_analyticAt ht z).meromorphicAt.pow 2).mul analyticAt_const.meromorphicAt)

theorem thetaSigmaRatio_analyticAt {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    AnalyticAt ℂ (sigmaRatio (thetaSigma t) a) z := by
  have hsa := mt (thetaSigma_zero_iff_lattice ht ht0 a).mp ha
  have hsz := mt (thetaSigma_zero_iff_lattice ht ht0 z).mp hz
  unfold sigmaRatio
  have hu := (thetaSigma_analyticAt ht0 (z-a)).comp (f := fun w => w-a) (by fun_prop)
  have hv := (thetaSigma_analyticAt ht0 (z+a)).comp (f := fun w => w+a) (by fun_prop)
  exact (hu.mul hv).div (((thetaSigma_analyticAt ht0 z).pow 2).mul analyticAt_const)
    (mul_ne_zero (pow_ne_zero 2 hsz) (pow_ne_zero 2 hsa))

theorem sigmaAdditionDifference_meromorphic {t : ℝ} (ht : 0 < t) (a : ℂ) :
    Meromorphic (sigmaAdditionDifference t ht a) := by
  let L := rhombicPeriodPair t ht
  have hf : Meromorphic (fun z => sigmaRatio (thetaSigma t) a z+L.weierstrassP z-L.weierstrassP a) := by
    intro z
    exact (((thetaSigmaRatio_meromorphic ht a z).add (L.meromorphic_weierstrassP z)).sub
      analyticAt_const.meromorphicAt)
  intro z
  refine (hf z).congr ?_
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds z)] with w hw hw'
  rw [sigmaAdditionDifference,ite_eq_right (by simp_all [L])]

theorem sigmaAdditionDifference_zero (t : ℝ) (ht : 0 < t) (a : ℂ) :
    sigmaAdditionDifference t ht a 0 = 0 := by simp [sigmaAdditionDifference]

theorem sigmaAdditionDifference_weighted {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    (sigmaAdditionDifference t ht0 a*(thetaSigma t)^2*(id : ℂ → ℂ)^2) =ᶠ[𝓝 0]
      sigmaAdditionNumerator (thetaSigma t) (fun z => thetaSigma t (z-a)) (fun z => thetaSigma t (z+a))
        (fun z => (rhombicPeriodPair t ht0).weierstrassPExcept 0 z-
          (rhombicPeriodPair t ht0).weierstrassP a) (thetaSigma t a) := by
  let L := rhombicPeriodPair t ht0
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases hz0 : z = 0
  · simp [hz0,sigmaAdditionNumerator,thetaSigma_zero]
  have hzL : z ∉ L.lattice := by simpa [hz0] using hz
  change z ∉ (rhombicPeriodPair t ht0).lattice at hzL
  have hsz := mt (thetaSigma_zero_iff_lattice ht ht0 z).mp hzL
  have hsa := mt (thetaSigma_zero_iff_lattice ht ht0 a).mp ha
  have hp : L.weierstrassP z = L.weierstrassPExcept 0 z+1/z^2 := by
    simpa using (L.weierstrassPExcept_add (0 : L.lattice) z).symm
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq,sigmaAdditionDifference,ite_eq_right hzL,
    sigmaRatio,sigmaAdditionNumerator]
  change (thetaSigma t (z-a)*thetaSigma t (z+a)/(thetaSigma t z^2*thetaSigma t a^2)+
    L.weierstrassP z-L.weierstrassP a)*thetaSigma t z^2*z^2 = _
  rw [hp]
  field_simp
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.sigmaAdditionDifference_weighted
