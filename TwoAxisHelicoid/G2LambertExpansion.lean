import TwoAxisHelicoid.RhombicLattice
import TwoAxisHelicoid.JacobiProductQuasiPeriod
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

namespace TwoAxisHelicoid
open Complex ArithmeticFunction EisensteinSeries
set_option maxHeartbeats 800000

noncomputable def rhombicUpperHalfPlane (t : ℝ) (ht : 0 < t) : UpperHalfPlane :=
  ⟨(1+I*t)/2,by simp [Complex.mul_im]; positivity⟩

theorem rhombic_lattice_G_four_eisenstein {t : ℝ} (ht : 0 < t) :
    (rhombicPeriodPair t ht).G 4 = (1/16 : ℂ)*
      ∑' v : Fin 2 → ℤ, eisSummand 4 v (rhombicUpperHalfPlane t ht) := by
  let L := rhombicPeriodPair t ht
  let e : (Fin 2 → ℤ) ≃ L.lattice :=
    (finTwoArrowEquiv ℤ).trans ((Equiv.prodComm ℤ ℤ).trans L.latticeEquivProd.symm.toEquiv)
  have he (v : Fin 2 → ℤ) : ((e v : L.lattice) : ℂ) =
      2*((v 0 : ℂ)*(rhombicUpperHalfPlane t ht : ℂ)+(v 1 : ℂ)) := by
    change ((L.latticeEquivProd.symm (v 1,v 0) : L.lattice) : ℂ) = _
    rw [L.latticeEquiv_symm_apply]
    dsimp [L,rhombicPeriodPair,rhombicUpperHalfPlane]
    ring
  change L.G 4 = _
  rw [PeriodPair.G,← e.tsum_eq,← tsum_mul_left]
  apply tsum_congr
  intro v
  rw [he]
  simp only [eisSummand,mul_pow,mul_inv,zpow_neg,zpow_ofNat]
  norm_num

theorem rhombic_eisenstein_nome {t : ℝ} (ht : 0 < t) :
    exp (2*(Real.pi : ℂ)*I*(rhombicUpperHalfPlane t ht : ℂ)) = jacobiNome t := by
  unfold rhombicUpperHalfPlane jacobiNome
  congr 1
  ring

/-- The lattice invariant appearing in the original proof has the literal
cubic Lambert series, with all sums justified by the Eisenstein expansion. -/
theorem actual_g2_lambert_expansion {t : ℝ} (ht : 0 < t) :
    (rhombicPeriodPair t ht).g₂ = ((Real.pi^4/12*(1+240*
      (∑' n : ℕ, (n+1 : ℝ)^3*(-Real.exp (-Real.pi*t))^(n+1)/
        (1-(-Real.exp (-Real.pi*t))^(n+1))))) : ℝ) := by
  have he := tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow
    (k := 4) (by norm_num) (by decide) (rhombicUpperHalfPlane t ht)
  rw [rhombic_eisenstein_nome ht] at he
  norm_num only [Nat.reduceSub,Nat.factorial,Nat.cast_ofNat] at he
  rw [riemannZeta_four] at he
  have hQ := jacobiNome_norm_lt_one ht
  have hs := tsum_pow_div_one_sub_eq_tsum_sigma hQ 3
  rw [← hs,tsum_pnat_eq_tsum_succ (f := fun n : ℕ =>
    (n : ℂ)^3*(jacobiNome t)^n/(1-(jacobiNome t)^n))] at he
  rw [PeriodPair.g₂,rhombic_lattice_G_four_eisenstein ht,he,jacobiNome_eq_neg_exp]
  have hcast : (∑' n : ℕ, ((n+1 : ℕ) : ℂ)^3*(-(Real.exp (-Real.pi*t) : ℂ))^(n+1)/
      (1-(-(Real.exp (-Real.pi*t) : ℂ))^(n+1))) =
      Complex.ofReal (∑' n : ℕ, (n+1 : ℝ)^3*(-Real.exp (-Real.pi*t))^(n+1)/
        (1-(-Real.exp (-Real.pi*t))^(n+1))) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    push_cast
    rfl
  rw [hcast]
  push_cast
  ring_nf
  norm_num [I_sq]
  apply tsum_congr
  intro n
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_g2_lambert_expansion
