import TwoAxisHelicoid.ThetaAllWeierstrass
import TwoAxisHelicoid.GaussPeriodicity
import TwoAxisHelicoid.WeierstrassDerivativeSigma

/-! Sigma, zeta, addition and Gauss formulas for every positive height. -/
namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaScaledJet thetaSigma thetaZeta thetaG thetaA

theorem thetaSigma_hasDerivAt_zero_of_pos {t : ℝ} (ht : 0 < t) : HasDerivAt (thetaSigma t) 1 0 := by
  have ht0 : 0 < t := by linarith
  simpa [thetaScaledJet_zero_at_zero,thetaScaledJet_one_ne_zero_of_pos ht] using thetaSigma_hasDerivAt ht0 0


theorem thetaSigma_zero_iff_lattice_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (z : ℂ) :
    thetaSigma t z = 0 ↔ z ∈ (rhombicPeriodPair t ht0).lattice := by
  rw [thetaSigma,div_eq_zero_iff,mul_eq_zero]
  simp only [Complex.exp_ne_zero,false_or,thetaScaledJet_one_ne_zero_of_pos ht,or_false]
  exact thetaScaledJet_zero_iff_lattice_of_pos ht ht0 z


theorem thetaZeta_hasDerivAt_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    HasDerivAt (thetaZeta t) (-(rhombicPeriodPair t ht0).weierstrassP z) z := by
  have hd := thetaZeta_hasDerivAt_log ht0 (mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht0 z).mp hz)
  rw [thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht0 hz] at hd
  simpa only [neg_add,neg_add_cancel_right] using hd


theorem thetaSigma_hasDerivAt_zeta_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    HasDerivAt (thetaSigma t) (thetaZeta t z*thetaSigma t z) z := by
  have hn := mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht0 z).mp hz
  have h1 := thetaScaledJet_one_ne_zero_of_pos ht
  convert thetaSigma_hasDerivAt ht0 z using 1
  unfold thetaZeta thetaSigma
  field_simp


theorem thetaZeta_add_half_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaZeta t (z+(1+I*t)) = thetaZeta t z+thetaEtaExpression t*(1+I*t)-Real.pi*I := by
  have hn : thetaJet t 0 (Real.pi*z/2) ≠ 0 := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp hz
  have harg : (Real.pi*(z+(1+I*t))/2:ℂ) = Real.pi*z/2+thetaComplexHalfPeriod t := by
    unfold thetaComplexHalfPeriod
    ring
  simp only [thetaZeta_quotient,harg,thetaQuotient_one_quasiperiod ht0 hn]
  ring


theorem thetaSigmaKernel_eq_thetaA_of_pos {t a : ℝ} (ht : 0 < t) (ht0 : 0 < t) (z : ℂ)
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaSigmaKernel t a z = thetaA t a z := by
  have hd := thetaScaledJet_one_ne_zero_of_pos ht
  have hs := mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht0 z).mp hz
  have hb := mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht0 (a:ℂ)).mp ha
  unfold thetaSigmaKernel thetaSigma thetaZeta
  rw [sigma_kernel_algebra (a:ℂ) z (thetaEtaExpression t)
    (thetaScaledJet t 1 z/thetaScaledJet t 0 z) (thetaScaledJet t 1 0)
    (thetaScaledJet t 0 (z-a)) (thetaScaledJet t 0 z) (thetaScaledJet t 0 (a:ℂ)) hd hs hb]
  exact (thetaA_eq_scaled t a z).symm


theorem thetaSigma_third_zero_of_pos {t : ℝ} (ht : 0 < t) : iteratedDeriv 3 (thetaSigma t) 0 = 0 := by
  have ht0 : 0 < t := by linarith
  have hD (n : ℕ) : iteratedDeriv n (thetaScaledJet t 0) 0 = thetaScaledJet t n 0 := by
    simpa using congrFun (thetaScaledJet_iteratedDeriv ht0 0 n) 0
  have he : thetaSigma t = fun z => quadraticExp (thetaEtaExpression t) z*
      thetaScaledJet t 0 z/thetaScaledJet t 1 0 := by unfold thetaSigma quadraticExp; rfl
  rw [he,iteratedDeriv_div_const,iteratedDeriv_fun_mul
    (quadraticExp_analyticAt (thetaEtaExpression t) 0).contDiffAt
    (thetaScaledJet_analyticAt ht0 0 0).contDiffAt]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,hD]
  norm_num [Nat.choose,quadraticExp_zero,quadraticExp_iterated_one_zero,
    quadraticExp_iterated_two_zero,thetaScaledJet_zero_at_zero,thetaScaledJet_one_ne_zero_of_pos ht]
  unfold thetaEtaExpression
  field_simp [thetaScaledJet_one_ne_zero_of_pos ht]
  ring


theorem thetaSigma_second_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    iteratedDeriv 2 (thetaSigma t) z =
      (thetaZeta t z^2-(rhombicPeriodPair t ht0).weierstrassP z)*thetaSigma t z := by
  have he : deriv (thetaSigma t) =ᶠ[𝓝 z] fun w => thetaZeta t w*thetaSigma t w := by
    filter_upwards [(rhombicPeriodPair t ht0).isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact (thetaSigma_hasDerivAt_zeta_of_pos ht ht0 hw).deriv
  have hd := (thetaZeta_hasDerivAt_of_pos ht ht0 hz).mul (thetaSigma_hasDerivAt_zeta_of_pos ht ht0 hz)
  have hd' := hd.congr_of_eventuallyEq he
  rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hd'.deriv]
  ring


theorem thetaSigma_wronskian_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    deriv (thetaSigma t) z^2-iteratedDeriv 2 (thetaSigma t) z*thetaSigma t z =
      (rhombicPeriodPair t ht0).weierstrassP z*thetaSigma t z^2 := by
  rw [(thetaSigma_hasDerivAt_zeta_of_pos ht ht0 hz).deriv,thetaSigma_second_of_pos ht ht0 hz]
  ring


theorem thetaSigmaRatio_analyticAt_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    AnalyticAt ℂ (sigmaRatio (thetaSigma t) a) z := by
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 a).mp ha
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 z).mp hz
  unfold sigmaRatio
  have hu := (thetaSigma_analyticAt ht0 (z-a)).comp (f := fun w => w-a) (by fun_prop)
  have hv := (thetaSigma_analyticAt ht0 (z+a)).comp (f := fun w => w+a) (by fun_prop)
  exact (hu.mul hv).div (((thetaSigma_analyticAt ht0 z).pow 2).mul analyticAt_const)
    (mul_ne_zero (pow_ne_zero 2 hsz) (pow_ne_zero 2 hsa))


theorem sigmaAdditionDifference_weighted_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a : ℂ}
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
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 z).mp hzL
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 a).mp ha
  have hp : L.weierstrassP z = L.weierstrassPExcept 0 z+1/z^2 := by
    simpa using (L.weierstrassPExcept_add (0 : L.lattice) z).symm
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq,sigmaAdditionDifference,ite_eq_right hzL,
    sigmaRatio,sigmaAdditionNumerator]
  change (thetaSigma t (z-a)*thetaSigma t (z+a)/(thetaSigma t z^2*thetaSigma t a^2)+
    L.weierstrassP z-L.weierstrassP a)*thetaSigma t z^2*z^2 = _
  rw [hp]
  field_simp
  ring


theorem thetaSigma_meromorphicOrder_zero_of_pos {t : ℝ} (ht : 0 < t) :
    meromorphicOrderAt (thetaSigma t) 0 = 1 := by
  have ht0 : 0 < t := by linarith
  have hf := thetaSigma_analyticAt ht0 0
  have hd : deriv (thetaSigma t) 0 ≠ 0 := by rw [(thetaSigma_hasDerivAt_zero_of_pos ht).deriv]; norm_num
  rw [hf.meromorphicOrderAt_eq,hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (thetaSigma_zero t) hd]
  norm_num


theorem sigmaAdditionDifference_analyticAt_zero_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    AnalyticAt ℂ (sigmaAdditionDifference t ht0 a) 0 := by
  let L := rhombicPeriodPair t ht0
  let U : ℂ → ℂ := fun z => thetaSigma t (z-a)
  let V : ℂ → ℂ := fun z => thetaSigma t (z+a)
  let g : ℂ → ℂ := fun z => L.weierstrassPExcept 0 z-L.weierstrassP a
  let W := sigmaAdditionDifference t ht0 a*(thetaSigma t)^2*(id : ℂ → ℂ)^2
  let N := sigmaAdditionNumerator (thetaSigma t) U V g (thetaSigma t a)
  have hf := thetaSigma_analyticAt ht0 0
  have hu : AnalyticAt ℂ U 0 :=
    (thetaSigma_analyticAt ht0 (0-a)).comp (f := fun z => z-a) (by fun_prop)
  have hv : AnalyticAt ℂ V 0 :=
    (thetaSigma_analyticAt ht0 (0+a)).comp (f := fun z => z+a) (by fun_prop)
  have hg : AnalyticAt ℂ g 0 := (L.analyticAt_weierstrassPExcept 0).sub analyticAt_const
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 a).mp ha
  have hN : AnalyticAt ℂ N 0 := by
    unfold N sigmaAdditionNumerator
    simp only [div_eq_mul_inv]
    fun_prop
  have he : W =ᶠ[𝓝 0] N := sigmaAdditionDifference_weighted_of_pos ht ht0 ha
  have hW : AnalyticAt ℂ W 0 := hN.congr he.symm
  have hu0 : U 0 = -thetaSigma t a := by simp [U,thetaSigma_neg]
  have hv0 : V 0 = thetaSigma t a := by simp [V]
  have hu1 : deriv U 0 = deriv (thetaSigma t) a := by
    simpa only [iteratedDeriv_one,zero_sub,thetaSigma_deriv_neg] using
      congrFun (iteratedDeriv_comp_sub_const 1 (thetaSigma t) a) 0
  have hv1 : deriv V 0 = deriv (thetaSigma t) a := by
    simpa only [iteratedDeriv_one,zero_add] using
      congrFun (iteratedDeriv_comp_add_const 1 (thetaSigma t) a) 0
  have hu2 : iteratedDeriv 2 U 0 = -iteratedDeriv 2 (thetaSigma t) a := by
    simpa only [zero_sub,thetaSigma_second_neg] using
      congrFun (iteratedDeriv_comp_sub_const 2 (thetaSigma t) a) 0
  have hv2 : iteratedDeriv 2 V 0 = iteratedDeriv 2 (thetaSigma t) a := by
    simpa only [zero_add] using congrFun (iteratedDeriv_comp_add_const 2 (thetaSigma t) a) 0
  have hg0 : g 0 = -L.weierstrassP a := by simp [g]
  have hvanish (n : ℕ) (hn : n < 5) : iteratedDeriv n W 0 = 0 := by
    rw [he.iteratedDeriv_eq n]
    exact sigmaAdditionNumerator_derivatives_vanish (thetaSigma t) U V g
      (thetaSigma t a) (deriv (thetaSigma t) a) (iteratedDeriv 2 (thetaSigma t) a) (L.weierstrassP a)
      hf hu hv hg hsa (thetaSigma_zero t) (thetaSigma_hasDerivAt_zero_of_pos ht).deriv
      (thetaSigma_second_zero ht0) (thetaSigma_third_zero_of_pos ht) hu0 hv0 hu1 hv1 hu2 hv2 hg0
      (thetaSigma_wronskian_of_pos ht ht0 ha) hn
  have horder : (5 : WithTop ℤ) ≤ meromorphicOrderAt W 0 := by
    rw [hW.meromorphicOrderAt_eq]
    exact ENat.monotone_map_iff.mpr Nat.mono_cast
      ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hW).mpr hvanish)
  have hD := sigmaAdditionDifference_meromorphic ht0 a 0
  have hM := hf.meromorphicAt
  have hId : MeromorphicAt (id : ℂ → ℂ) 0 := analyticAt_id.meromorphicAt
  change (5 : WithTop ℤ) ≤ meromorphicOrderAt
    (sigmaAdditionDifference t ht0 a*(thetaSigma t)^2*(id : ℂ → ℂ)^2) 0 at horder
  rw [meromorphicOrderAt_mul (hD.mul (hM.pow 2)) (hId.pow 2),
    meromorphicOrderAt_mul hD (hM.pow 2),meromorphicOrderAt_pow hM,
    meromorphicOrderAt_pow hId,thetaSigma_meromorphicOrder_zero_of_pos ht,meromorphicOrderAt_id] at horder
  have hpos : (1 : WithTop ℤ) ≤ meromorphicOrderAt (sigmaAdditionDifference t ht0 a) 0 := by
    rw [← WithTop.add_le_add_iff_right (z := 4) (by simp)]
    norm_num only [mul_one,add_assoc] at horder ⊢
    exact horder
  exact AnalyticAt.of_meromorphicOrderAt_pos (one_pos.trans_le hpos)
    (sigmaAdditionDifference_zero t ht0 a)


theorem sigmaAdditionDifference_analyticAt_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) (z : ℂ) :
    AnalyticAt ℂ (sigmaAdditionDifference t ht0 a) z := by
  let L := rhombicPeriodPair t ht0
  by_cases hz : z ∈ L.lattice
  · have h0 := sigmaAdditionDifference_analyticAt_zero_of_pos ht ht0 ha
    rw [← sub_self z] at h0
    convert h0.comp (f := fun w => w-z) (by fun_prop) using 1
    funext w
    exact (sigmaAdditionDifference_sub_lattice ht0 a w ⟨z,hz⟩).symm
  · have hf : AnalyticAt ℂ (fun w => sigmaRatio (thetaSigma t) a w+L.weierstrassP w-L.weierstrassP a) z :=
      ((thetaSigmaRatio_analyticAt_of_pos ht ht0 ha hz).add (L.analyticOnNhd_weierstrassP z hz)).sub analyticAt_const
    apply hf.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w ∉ (rhombicPeriodPair t ht0).lattice at hw
    simp only [sigmaAdditionDifference,ite_eq_right hw]
    rfl


theorem sigmaAdditionDifference_eq_zero_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) (z : ℂ) : sigmaAdditionDifference t ht0 a z = 0 := by
  let L := rhombicPeriodPair t ht0
  have hd : Differentiable ℂ (sigmaAdditionDifference t ht0 a) :=
    fun w => (sigmaAdditionDifference_analyticAt_of_pos ht ht0 ha w).differentiableAt
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice (sigmaAdditionDifference t ht0 a)
    hd.continuous (fun x w hw => sigmaAdditionDifference_add_lattice ht0 a x ⟨w,hw⟩)).isBounded
  exact (hd.apply_eq_apply_of_bounded hb z 0).trans (sigmaAdditionDifference_zero t ht0 a)


theorem thetaSigma_addition_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaSigma t (z-a)*thetaSigma t (z+a)/(thetaSigma t z^2*thetaSigma t a^2) =
      (rhombicPeriodPair t ht0).weierstrassP a-(rhombicPeriodPair t ht0).weierstrassP z := by
  have h := sigmaAdditionDifference_eq_zero_of_pos ht ht0 ha z
  rw [sigmaAdditionDifference,ite_eq_right hz,sigmaRatio] at h
  linear_combination h


theorem thetaSigmaRatio_hasDerivAt_self_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    HasDerivAt (sigmaRatio (thetaSigma t) a) (thetaSigma t (2*a)/thetaSigma t a^4) a := by
  have hn := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 a).mp ha
  have h0 : HasDerivAt (thetaSigma t) 1 (a-a) := by
    simpa only [sub_self] using thetaSigma_hasDerivAt_zero_of_pos ht
  have hm := h0.comp (h := fun z : ℂ => z-a) a ((hasDerivAt_id a).sub_const a)
  have hp := (thetaSigma_hasDerivAt ht0 (a+a)).comp (h := fun z : ℂ => z+a) a ((hasDerivAt_id a).add_const a)
  have hd := ((thetaSigma_hasDerivAt ht0 a).pow 2).mul_const (thetaSigma t a^2)
  have hr := (hm.mul hp).div hd (mul_ne_zero (pow_ne_zero 2 hn) (pow_ne_zero 2 hn))
  convert hr using 1
  · rfl
  · simp only [Pi.mul_apply,Pi.pow_apply,Function.comp_apply,sub_self,thetaSigma_zero,zero_mul,sub_zero,add_zero,
      one_mul,mul_one,show a+a = 2*a by ring]
    field_simp


theorem rhombic_weierstrassP_derivative_sigma_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    (rhombicPeriodPair t ht0).derivWeierstrassP a = -thetaSigma t (2*a)/thetaSigma t a^4 := by
  let L := rhombicPeriodPair t ht0
  have he : sigmaRatio (thetaSigma t) a =ᶠ[𝓝 a] fun z => L.weierstrassP a-L.weierstrassP z := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds ha] with z hz
    exact thetaSigma_addition_of_pos ht ht0 ha hz
  have hr := (thetaSigmaRatio_hasDerivAt_self_of_pos ht ht0 ha).congr_of_eventuallyEq he.symm
  have hp := (rhombic_weierstrassP_hasDerivAt ht0 ha).const_sub (L.weierstrassP a)
  have h := hr.unique hp
  linear_combination h


theorem rhombic_weierstrassP_critical_iff_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    (rhombicPeriodPair t ht0).derivWeierstrassP a = 0 ↔ 2*a ∈ (rhombicPeriodPair t ht0).lattice := by
  have hn := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 a).mp ha
  rw [rhombic_weierstrassP_derivative_sigma_of_pos ht ht0 ha,div_eq_zero_iff,neg_eq_zero]
  simp only [pow_ne_zero 4 hn,or_false]
  exact thetaSigma_zero_iff_lattice_of_pos ht ht0 (2*a)


theorem thetaGauss_height_sigma_of_pos {t a : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c : ℝ) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice)
    (hzp : z+a ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaGauss t a 1 z*(I*c*((rhombicPeriodPair t ht0).weierstrassP z-
      (rhombicPeriodPair t ht0).weierstrassP a)) = (c:ℂ)*thetaSigmaKernel t a z := by
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 (a:ℂ)).mp ha
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 z).mp hz
  have hsp := mt (thetaSigma_zero_iff_lattice_of_pos ht ht0 (z+a)).mp hzp
  have hAdd := thetaSigma_addition_of_pos ht ht0 ha hz
  rw [← neg_sub ((rhombicPeriodPair t ht0).weierstrassP a)
    ((rhombicPeriodPair t ht0).weierstrassP z),← hAdd]
  simp only [thetaGauss,thetaSigmaKernel,Int.cast_one,mul_one]
  field_simp
  ring_nf
  simp only [I_sq]
  ring


theorem thetaGauss_height_kernel_of_pos {t a : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c : ℝ) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice)
    (hzp : z+a ∉ (rhombicPeriodPair t ht0).lattice) (hG : thetaG t a = 0) :
    thetaGauss t a 1 z*(I*c*((rhombicPeriodPair t ht0).weierstrassP z-
      ((Real.pi/t:ℝ)-thetaEtaExpression t))) = (c:ℂ)*thetaA t a z := by
  have he := thetaG_eq_weierstrassP_of_pos ht ht0 a ha
  rw [hG] at he
  have hu : ((Real.pi/t:ℝ):ℂ)-thetaEtaExpression t = (rhombicPeriodPair t ht0).weierstrassP a := by
    linear_combination he
  rw [hu,thetaGauss_height_sigma_of_pos ht ht0 c ha hz hzp,thetaSigmaKernel_eq_thetaA_of_pos ht ht0 z ha hz]


theorem thetaGauss_period_half_of_pos {t a : ℝ} (ht : 0 < t) (ht0 : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaGauss t a m (z+(1+I*t)) = thetaGauss t a m z := by
  have h := thetaGauss_quasiperiod (t := t) (a := a) m (z := z)
    (w := 1+I*t) (k := thetaEtaExpression t*(1+I*t)-Real.pi*I)
    (thetaSigma_add_half ht0) (by simpa only [add_sub_assoc] using thetaZeta_add_half_of_pos ht ht0 hz)
  have he : (2*(m:ℂ)*(thetaEtaExpression t*(1+I*t)-
      (thetaEtaExpression t*(1+I*t)-Real.pi*I))) = (m:ℂ)*(2*Real.pi*I) := by ring
  rw [he,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow,one_mul] at h
  exact h


end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_addition_of_pos
#print axioms TwoAxisHelicoid.thetaGauss_height_kernel_of_pos
#print axioms TwoAxisHelicoid.thetaGauss_period_half_of_pos
