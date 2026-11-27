import TwoAxisHelicoid.WeierstrassSpinors
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaSigma thetaZeta

theorem exists_spinor_normalizing_constant {t a c : ℝ} (ht : 0 < t)
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice) (hc : c ≠ 0) :
    ∃ C : ℂ, C ≠ 0 ∧ C^2 = (c : ℂ)/(2*thetaSigma t a^2) := by
  have hσ := mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp ha
  have hnon : (c : ℂ)/(2*thetaSigma t a^2) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr hc) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hσ))
  refine ⟨exp (log ((c : ℂ)/(2*thetaSigma t a^2))/2),exp_ne_zero _,?_⟩
  rw [← exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 2*(log ((c : ℂ)/(2*thetaSigma t a^2))/2) =
    log ((c : ℂ)/(2*thetaSigma t a^2)) by ring,exp_log hnon]

noncomputable def spinorPrefactor (t a : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  exp (spinorExponent t a m z)/thetaSigma t z

theorem spinorPrefactor_analyticAt {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : AnalyticAt ℂ (spinorPrefactor t a m) z :=
  (spinorExponent_analyticAt ht m hz).cexp.div (thetaSigma_analyticAt ht z)
    (mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz)

theorem spinorPrefactor_ne_zero {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : spinorPrefactor t a m z ≠ 0 :=
  div_ne_zero (exp_ne_zero _) (mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz)

theorem thetaSpinor_at_a (t a : ℝ) (m : ℤ) : thetaSpinor t a m a = 0 := by
  simp [thetaSpinor,thetaSigma_zero]

theorem thetaSpinor_hasDerivAt_a {t a : ℝ} (ht : 0 < t)
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice) (m : ℤ) :
    HasDerivAt (thetaSpinor t a m) (spinorPrefactor t a m a) a := by
  have hσ0 : HasDerivAt (thetaSigma t) 1 ((a : ℂ)-a) := by
    simpa only [sub_self] using thetaSigma_hasDerivAt_zero_of_pos ht
  have hσ := hσ0.comp (h := fun z : ℂ => z-a) (a : ℂ)
    ((hasDerivAt_id (a : ℂ)).sub_const (a : ℂ))
  have hp := (spinorPrefactor_analyticAt (a := a) ht m ha).differentiableAt.hasDerivAt
  have hd := hp.mul hσ
  convert hd using 1
  · funext z
    dsimp [thetaSpinor,spinorPrefactor]
    ring
  · simp only [Function.comp_apply,sub_self,thetaSigma_zero,mul_zero,zero_add,mul_one]

theorem thetaSpinor_simple_zero_a {t a : ℝ} (ht : 0 < t)
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice) (m : ℤ) :
    thetaSpinor t a m a = 0 ∧ deriv (thetaSpinor t a m) a ≠ 0 := by
  refine ⟨thetaSpinor_at_a t a m,?_⟩
  rw [(thetaSpinor_hasDerivAt_a ht ha m).deriv]
  exact spinorPrefactor_ne_zero ht m ha

theorem weierstrassSpinors_analyticAt {t a : ℝ} (ht : 0 < t) (m : ℤ) (C : ℂ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    AnalyticAt ℂ (weierstrassSpinorOne t a m C) z ∧
    AnalyticAt ℂ (weierstrassSpinorTwo t a m C) z :=
  ⟨analyticAt_const.mul (thetaSpinor_analyticAt ht m hz),
    analyticAt_const.mul (thetaSpinor_analyticAt ht (-m) hz)⟩

noncomputable def spinorCoordinateData (t a : ℝ) (m : ℤ) (C z : ℂ) : Fin 3 → ℂ :=
  let s₁ := weierstrassSpinorOne t a m C z
  let s₂ := weierstrassSpinorTwo t a m C z
  ![s₂^2-s₁^2,I*(s₂^2+s₁^2),2*s₁*s₂]

theorem spinorCoordinateData_analyticAt {t a : ℝ} (ht : 0 < t) (m : ℤ) (C : ℂ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    AnalyticAt ℂ (spinorCoordinateData t a m C) z := by
  obtain ⟨h1,h2⟩ := weierstrassSpinors_analyticAt ht m C hz
  apply AnalyticAt.pi
  intro i
  fin_cases i <;> dsimp [spinorCoordinateData] <;> fun_prop

theorem spinorCoordinateData_null (t a : ℝ) (m : ℤ) (C z : ℂ) :
    (spinorCoordinateData t a m C z 0)^2+(spinorCoordinateData t a m C z 1)^2+
      (spinorCoordinateData t a m C z 2)^2 = 0 := by
  dsimp [spinorCoordinateData]
  ring_nf
  simp only [I_sq]
  ring

theorem spinorCoordinateData_ne_zero {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C z : ℂ} (hC : C ≠ 0)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : spinorCoordinateData t a m C z ≠ 0 := by
  intro he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp only [spinorCoordinateData,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply] at h0 h1
  have hsum := (mul_eq_zero.mp h1).resolve_left I_ne_zero
  have hz1 : (weierstrassSpinorOne t a m C z)^2 = 0 := by linear_combination (hsum-h0)/2
  have hz2 : (weierstrassSpinorTwo t a m C z)^2 = 0 := by linear_combination (hsum+h0)/2
  rcases weierstrassSpinor_pair_not_both_zero ht ha m hC hz with h | h
  · exact h ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hz1)
  · exact h ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hz2)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_spinor_normalizing_constant
#print axioms TwoAxisHelicoid.thetaSpinor_simple_zero_a
#print axioms TwoAxisHelicoid.spinorCoordinateData_ne_zero
