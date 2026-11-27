import TwoAxisHelicoid.ActualGlobalImmersion
import TwoAxisHelicoid.NullGaussDivisor
import TwoAxisHelicoid.AlignedEndDoublePoles

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate
attribute [local irreducible] thetaA

/-- The finite simple zero and pole belong to the Gauss map calculated
from the derivatives of the actual closed immersion. -/
theorem closed_immersion_gauss_divisor {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hc : c ≠ 0) (hG : thetaG t a = 0) (hH : thetaHorizontalPeriod t a = 0) :
    GaussZeroPoleData t a ht (immersionGaussMap (actualGlobalImmersion t a c ht)) := by
  let L := rhombicPeriodPair t ht
  let p := coordinateData t a c ht
  let X := actualGlobalImmersion t a c ht
  let g := immersionGaussMap X
  have hnull : TwoAxisNullDifferential L p :=
    ⟨fun z w hw => coordinateData_add_lattice ht z ⟨w,hw⟩,fun _ hz => coordinateData_null ht ha hz,
     fun _ hz => coordinateData_ne_zero ht ha hc hz,fun z _ => coordinateData_neg ht z,
     fun z _ => coordinateData_conj ht z⟩
  have han := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have hz : thetaA t a a = 0 := (thetaA_zero_iff_shift_lattice ht han han).mpr (by simp)
  have hn := (thetaA_pair_not_both_zero ht ha han).resolve_left (not_ne_iff.mpr hz)
  have hC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hm : nullHorizontalMinus (p a) ≠ 0 := by
    have he : nullHorizontalMinus (p a) = -(c:ℂ)*thetaA t a (-a) := by
      dsimp [p,coordinateData,nullHorizontalMinus]
      ring_nf
      simp only [I_sq]
      ring
    rw [he]
    exact mul_ne_zero (neg_ne_zero.mpr hC) hn
  have D := null_gauss_zero_pole_data ht ha hnull (fun _ hx j => (analyticAt_pi_iff.mp (coordinateData_analyticAt ht hx)) j)
    (K := I*c) (mul_ne_zero I_ne_zero hC) (fun _ _ => rfl) hm
  have heq (z : ℂ) (hz : z ∉ L.lattice) : g z = nullGauss (p z) := by
    have d := ((actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 z hz).1
    have he := (immersionComplexCoefficient_hasFDerivAt d.differentiableAt).unique d
    apply congrArg nullGauss
    funext j
    apply Complex.ext
    · simpa using congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f 1 j) he
    · simpa using congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f I j) he
  have hloc z (hz : z ∉ L.lattice) : g =ᶠ[𝓝 z] fun w => nullGauss (p w) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact heq w hw
  have han' : -(a:ℂ) ∉ L.lattice := by simpa [L] using han
  have hi : (fun z => (g z)⁻¹) =ᶠ[𝓝 (-(a:ℂ))] fun z => (nullGauss (p z))⁻¹ :=
    (hloc _ han').mono fun z hz => congrArg Inv.inv hz
  have away z (hz : z ∉ gaussLogPoleSet L a) := ((not_mem_gaussLogPoleSet L a z).mp hz).1
  change GaussZeroPoleData t a ht g
  refine ⟨fun z hz => (D.analytic z hz).congr (hloc z (away z hz)).symm,
    fun z hz => (heq z (away z hz)).trans_ne (D.nonzero z hz),?_,?_,?_,
    D.positive_analytic.congr (hloc _ han).symm,(heq _ han).trans D.positive_zero,?_,
    D.negative_analytic.congr hi.symm,hi.eq_of_nhds.trans D.negative_zero,?_⟩
  · intro z w hw hz
    have hzw : z+w ∉ L.lattice := by
      intro h
      exact away z hz (by simpa using L.lattice.sub_mem h hw)
    rw [heq _ hzw,heq _ (away z hz)]
    exact D.periodic z w hw hz
  · intro z hz
    have hcz : conj z ∉ L.lattice := by
      intro h
      exact away z hz (by simpa using rhombic_conj_mem ht h)
    rw [heq _ hcz,heq _ (away z hz)]
    exact D.conjugation z hz
  · intro z hz
    have hnz : -z ∉ L.lattice := by simpa using away z hz
    rw [heq _ hnz,heq _ (away z hz)]
    exact D.neg_product z hz
  · simpa only [(hloc _ han).deriv_eq] using D.positive_simple
  · simpa only [hi.deriv_eq] using D.negative_simple

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.closed_immersion_gauss_divisor
