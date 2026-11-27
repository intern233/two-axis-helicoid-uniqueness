import TwoAxisHelicoid.ZetaReciprocal
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta

theorem thetaSigma_reciprocal_off_lattice {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaSigma t z = (I*t)*thetaSigma (1/t) (z/(I*t)) := by
  let L := rhombicPeriodPair t ht
  let B : ℂ → ℂ := fun w => (I*t)*thetaSigma (1/t) (w/(I*t))
  let D : ℂ → ℂ := fun w => thetaSigma t w/B w
  have htinv := one_div_pos.mpr ht
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  have hBne (w : ℂ) (hw : w ∉ L.lattice) : B w ≠ 0 :=
    mul_ne_zero hi (mt (thetaSigma_zero_iff_lattice_of_pos htinv htinv _).mp
      (reciprocal_not_mem_lattice ht hw))
  have hd (w : ℂ) (hw : w ∉ L.lattice) : HasDerivAt D 0 w := by
    have hs := ((thetaSigma_hasDerivAt_zeta_of_pos htinv htinv
      (reciprocal_not_mem_lattice ht hw)).comp (h := fun v : ℂ => v/(I*t)) w
      ((hasDerivAt_id w).div_const (I*t))).const_mul (I*t)
    have h := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hw).div hs (hBne w hw)
    convert h using 1
    · rfl
    · simp only [Function.comp_apply]
      rw [thetaZeta_reciprocal ht hw]
      field_simp
      ring
  have hconn : IsPreconnected (L.lattice:Set ℂ)ᶜ := by
    refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact countable_of_Lindelof_of_discrete (X := L.lattice)
  have hconst (w : ℂ) (hw : w ∉ L.lattice) : D w = D z :=
    L.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero hconn
      (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hd v hv).deriv) hw hz
  have hB0 : B 0 = 0 := by simp [B,thetaSigma_zero]
  have hdB0 : HasDerivAt B 1 0 := by
    have h0 : HasDerivAt (thetaSigma (1/t)) 1 ((0:ℂ)/(I*t)) := by
      simpa only [zero_div] using thetaSigma_hasDerivAt_zero_of_pos htinv
    have h := (h0.comp
      (h := fun v : ℂ => v/(I*t)) 0 ((hasDerivAt_id (0:ℂ)).div_const (I*t))).const_mul (I*t)
    unfold B
    simpa only [Function.comp_def,one_mul,mul_one_div_cancel hi] using h
  have htS : Tendsto (fun w : ℂ => thetaSigma t w/w) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [slope_fun_def_field,thetaSigma_zero,sub_zero] using
      (thetaSigma_hasDerivAt_zero_of_pos ht).tendsto_slope
  have htB : Tendsto (fun w : ℂ => B w/w) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [slope_fun_def_field,hB0,sub_zero] using hdB0.tendsto_slope
  have hratio := htS.div htB (by norm_num : (1:ℂ) ≠ 0)
  change Tendsto (fun w : ℂ => (thetaSigma t w/w)/(B w/w)) (𝓝[≠] 0) (𝓝 ((1:ℂ)/1)) at hratio
  simp only [div_one] at hratio
  have hDlim : Tendsto D (𝓝[≠] 0) (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact div_div_div_cancel_right₀ hw _ _
  have hreg : ∀ᶠ w : ℂ in 𝓝[≠] 0, w ∉ L.lattice := by
    have hr : ∀ᶠ w : ℂ in 𝓝[≠] 0, w ∉ (L.lattice:Set ℂ) \ {0} :=
      nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)
    filter_upwards [hr,self_mem_nhdsWithin] with w hw hw0
    exact fun h => hw ⟨h,hw0⟩
  have hDeq : D =ᶠ[𝓝[≠] 0] fun _ => D z := hreg.mono fun w hw => hconst w hw
  have hDone : D z = 1 :=
    (tendsto_nhds_unique hDlim (tendsto_const_nhds.congr' hDeq.symm)).symm
  simpa only [one_mul] using (div_eq_iff (hBne z hz)).mp hDone

theorem thetaSigma_reciprocal {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaSigma t z = (I*t)*thetaSigma (1/t) (z/(I*t)) := by
  by_cases hz : z ∈ (rhombicPeriodPair t ht).lattice
  · have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
    have hs : z/(I*t) ∈ (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).lattice := by
      apply (rhombic_reciprocal_mem_iff ht _).mpr
      rw [mul_div_cancel₀ _ hi]
      exact hz
    rw [(thetaSigma_zero_iff_lattice_of_pos ht ht z).mpr hz,
      (thetaSigma_zero_iff_lattice_of_pos (one_div_pos.mpr ht) (one_div_pos.mpr ht) _).mpr hs,mul_zero]
  · exact thetaSigma_reciprocal_off_lattice ht hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_reciprocal
