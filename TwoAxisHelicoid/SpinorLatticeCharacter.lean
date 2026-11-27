import TwoAxisHelicoid.SpinorSectionParity
import TwoAxisHelicoid.UnitSpinorFrameCover

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000

noncomputable def paritySign (g : ZMod 2) : ℂ := if g = 0 then 1 else -1

theorem paritySign_zero : paritySign 0 = 1 := by simp [paritySign]
theorem paritySign_one : paritySign 1 = -1 := by norm_num [paritySign]

theorem paritySign_add (g h : ZMod 2) :
    paritySign (g+h) = paritySign g*paritySign h := by
  rcases zmod_two_cases g with rfl | rfl <;> rcases zmod_two_cases h with rfl | rfl <;>
    simp only [zero_add,add_zero,show (1 : ZMod 2)+1 = 0 from by decide,
      paritySign_zero,paritySign_one] <;> norm_num

theorem paritySign_sq (g : ZMod 2) : paritySign g^2 = 1 := by
  rcases zmod_two_cases g with rfl | rfl <;> norm_num [paritySign]

theorem paritySign_intCast (n : ℤ) : paritySign (n : ZMod 2) = (-1 : ℂ)^n := by
  simp [paritySign,ZMod.intCast_eq_zero_iff_even,neg_one_zpow_eq_ite]

noncomputable def latticeSpinParity (L : PeriodPair) (m : ℤ) : L.lattice →+ ZMod 2 where
  toFun ω := (m*(L.latticeEquivProd ω).2 : ℤ)
  map_zero' := by simp
  map_add' ω ν := by
    simp only [map_add,Prod.snd_add,mul_add,Int.cast_add]

theorem latticeSpinParity_coordinates (L : PeriodPair) (m : ℤ) (p : ℤ × ℤ) :
    latticeSpinParity L m (L.latticeEquivProd.symm p) = (m*p.2 : ℤ) := by
  change ((m*(L.latticeEquivProd (L.latticeEquivProd.symm p)).2 : ℤ) : ZMod 2) = _
  rw [L.latticeEquivProd.apply_symm_apply]

theorem latticeSpinParity_sign (L : PeriodPair) (m : ℤ) (ω : L.lattice) :
    paritySign (latticeSpinParity L m ω) = integerSpinCharacter m (L.latticeEquivProd ω) :=
  paritySign_intCast _

theorem multiplicative_quasiperiod_int {f : ℂ → ℂ} {p ε : ℂ}
    (hε : ε ≠ 0) (hf : ∀ z, f (z+p) = ε*f z) (n : ℤ) (z : ℂ) :
    f (z+(n : ℂ)*p) = ε^n*f z := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have he : z+(((n : ℤ)+1 : ℤ) : ℂ)*p = (z+((n : ℤ) : ℂ)*p)+p := by
        push_cast
        ring
      rw [he,hf,ih,zpow_add₀ hε,zpow_one]
      ring
  | pred n ih =>
      have hh := hf (z+((-(n : ℤ)-1 : ℤ) : ℂ)*p)
      have he : z+((-(n : ℤ)-1 : ℤ) : ℂ)*p+p = z+((-(n : ℤ) : ℤ) : ℂ)*p := by
        push_cast
        ring
      rw [he,ih] at hh
      calc
        _ = (ε^(-(n : ℤ))*f z)/ε := by
          apply (eq_div_iff hε).mpr
          linear_combination -hh
        _ = _ := by
          rw [zpow_sub₀ hε,zpow_one]
          ring

theorem thetaSpinor_multiplier_half_all {t a : ℝ} (ht : 0 < t) (m : ℤ) (z : ℂ) :
    thetaSpinor t a m (z+(1+I*t)) = (-1 : ℂ)^m*thetaSpinor t a m z := by
  by_cases hz : z ∈ (rhombicPeriodPair t ht).lattice
  · have hw : 1+I*t ∈ (rhombicPeriodPair t ht).lattice := by
      apply PeriodPair.mem_lattice.mpr
      exact ⟨0,1,by simp [rhombicPeriodPair]⟩
    have hzσ := (thetaSigma_zero_iff_lattice_of_pos ht ht z).mpr hz
    have hzwσ := (thetaSigma_zero_iff_lattice_of_pos ht ht (z+(1+I*t))).mpr
      ((rhombicPeriodPair t ht).lattice.add_mem hz hw)
    simp [thetaSpinor,hzσ,hzwσ]
  · exact thetaSpinor_multiplier_half ht m hz

theorem thetaSpinor_multiplier_coordinates {t a : ℝ} (ht : 0 < t) (m : ℤ)
    (p : ℤ × ℤ) (z : ℂ) :
    thetaSpinor t a m (z+(p.1 : ℂ)*2+(p.2 : ℂ)*(1+I*t)) =
      integerSpinCharacter m p*thetaSpinor t a m z := by
  rw [multiplicative_quasiperiod_int (zpow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
    (thetaSpinor_multiplier_half_all ht m) p.2 (z+(p.1 : ℂ)*2)]
  have hp := (thetaSpinor_period_two t a m).zsmul p.1 z
  simp only [zsmul_eq_mul] at hp
  rw [hp,← zpow_mul]
  rfl

theorem thetaSpinor_multiplier_lattice {t a : ℝ} (ht : 0 < t) (m : ℤ)
    (ω : (rhombicPeriodPair t ht).lattice) (z : ℂ) :
    thetaSpinor t a m (z+ω.1) =
      paritySign (latticeSpinParity (rhombicPeriodPair t ht) m ω)*thetaSpinor t a m z := by
  let L := rhombicPeriodPair t ht
  let p := L.latticeEquivProd ω
  have hω : ω.1 = (p.1 : ℂ)*2+(p.2 : ℂ)*(1+I*t) := by
    have h := L.latticeEquiv_symm_apply p
    rw [L.latticeEquivProd.symm_apply_apply] at h
    exact h
  rw [hω,latticeSpinParity_sign]
  simpa only [add_assoc] using thetaSpinor_multiplier_coordinates ht m p z

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSpinor_multiplier_lattice

