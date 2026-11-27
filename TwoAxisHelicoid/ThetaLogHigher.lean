import TwoAxisHelicoid.ThetaAllWeierstrass
import TwoAxisHelicoid.ZetaHalfPeriod
import TwoAxisHelicoid.WeierstrassDerivativeSigma

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaQuotient thetaLogSecond

noncomputable def thetaLogThird (t : ℝ) (z : ℂ) : ℂ :=
  (Real.pi^3/8:ℂ)*(3*thetaQuotient t 1 (Real.pi*z/2)*thetaQuotient t 2 (Real.pi*z/2)-
    2*thetaQuotient t 1 (Real.pi*z/2)^3-thetaQuotient t 3 (Real.pi*z/2))

noncomputable def thetaLogFourth (t : ℝ) (z : ℂ) : ℂ :=
  (Real.pi^4/16:ℂ)*(3*thetaQuotient t 2 (Real.pi*z/2)^2-
    12*thetaQuotient t 1 (Real.pi*z/2)^2*thetaQuotient t 2 (Real.pi*z/2)+
    6*thetaQuotient t 1 (Real.pi*z/2)^4+
    4*thetaQuotient t 1 (Real.pi*z/2)*thetaQuotient t 3 (Real.pi*z/2)-
    thetaQuotient t 4 (Real.pi*z/2))

theorem thetaQuotient_z_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) {z : ℂ}
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0) :
    HasDerivAt (fun w : ℂ => thetaQuotient t j (Real.pi*w/2))
      ((Real.pi/2:ℂ)*(thetaQuotient t (j+1) (Real.pi*z/2)-
        thetaQuotient t j (Real.pi*z/2)*thetaQuotient t 1 (Real.pi*z/2))) z := by
  have h := (thetaQuotient_hasDerivAt ht j _ hz).comp
    (h := fun w : ℂ => Real.pi*w/2) z (((hasDerivAt_id z).const_mul (Real.pi:ℂ)).div_const 2)
  convert h using 1
  · rfl
  · simp only [mul_one]
    ring

theorem thetaLogSecond_hasDerivAt_of_pos {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0) :
    HasDerivAt (thetaLogSecond t) (thetaLogThird t z) z := by
  have h1 := thetaQuotient_z_hasDerivAt ht 1 hz
  have h2 := thetaQuotient_z_hasDerivAt ht 2 hz
  have h := ((h1.pow 2).sub h2).const_mul (Real.pi^2/4:ℂ)
  convert h using 1
  · funext w
    simp only [thetaLogSecond,Pi.pow_apply,Pi.sub_apply]
  · unfold thetaLogThird
    norm_num
    ring

theorem thetaLogThird_hasDerivAt {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0) :
    HasDerivAt (thetaLogThird t) (thetaLogFourth t z) z := by
  have h1 := thetaQuotient_z_hasDerivAt ht 1 hz
  have h2 := thetaQuotient_z_hasDerivAt ht 2 hz
  have h3 := thetaQuotient_z_hasDerivAt ht 3 hz
  have h := ((((h1.mul h2).const_mul 3).sub ((h1.pow 3).const_mul 2)).sub h3).const_mul (Real.pi^3/8:ℂ)
  convert h using 1
  · funext w
    simp only [thetaLogThird,Pi.mul_apply,Pi.pow_apply,Pi.sub_apply]
    ring
  · unfold thetaLogFourth
    norm_num
    ring

theorem thetaLogThird_eq_weierstrassP_deriv {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaLogThird t z = (rhombicPeriodPair t ht).derivWeierstrassP z := by
  have hden := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp hz
  have hd := thetaLogSecond_hasDerivAt_of_pos ht hden
  have hp := (rhombic_weierstrassP_hasDerivAt ht hz).add_const (thetaEtaExpression t)
  have he : thetaLogSecond t =ᶠ[𝓝 z]
      fun w => (rhombicPeriodPair t ht).weierstrassP w+thetaEtaExpression t := by
    filter_upwards [(rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hw
  exact hd.unique (hp.congr_of_eventuallyEq he)

theorem thetaLogFourth_eq_weierstrassP_second {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaLogFourth t z = deriv ((rhombicPeriodPair t ht).derivWeierstrassP) z := by
  have hden := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp hz
  have he : thetaLogThird t =ᶠ[𝓝 z] (rhombicPeriodPair t ht).derivWeierstrassP := by
    filter_upwards [(rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact thetaLogThird_eq_weierstrassP_deriv ht hw
  exact ((thetaLogThird_hasDerivAt ht hden).congr_of_eventuallyEq he.symm).deriv.symm

theorem thetaQuotient_one_half_pi (t : ℝ) : thetaQuotient t 1 (Real.pi/2) = 0 := by
  simp only [thetaQuotient,thetaJet_one_half_pi,zero_div]

theorem thetaLogFourth_one (t : ℝ) :
    thetaLogFourth t 1 = (Real.pi^4/16:ℂ)*
      (3*thetaQuotient t 2 (Real.pi/2)^2-thetaQuotient t 4 (Real.pi/2)) := by
  simp [thetaLogFourth,thetaQuotient_one_half_pi]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaLogFourth_eq_weierstrassP_second
