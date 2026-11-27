import TwoAxisHelicoid.PdfVerticalGridSound
import TwoAxisHelicoid.ExpEnclosure

namespace TwoAxisHelicoid.PdfVertical.Grid

theorem contains_taylor {a : Grid} {x : ℝ} (ha : a.Contains x) (n : ℕ) :
    (taylor a n).1.Contains (expPolynomial n x) ∧
    (taylor a n).2.Contains (x^n/(n.factorial:ℝ)) := by
  induction n with
  | zero => simpa only [taylor,expPolynomial,Finset.range_zero,Finset.sum_empty,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,
      Int.cast_zero,Int.cast_one] using And.intro (contains_int 0) (contains_int 1)
  | succ n ih =>
    obtain ⟨s,p⟩ := ih
    change ((taylor a n).1.add (taylor a n).2).Contains (expPolynomial (n+1) x) ∧ _
    refine ⟨?_,?_⟩
    · simpa only [expPolynomial,Finset.sum_range_succ] using contains_add s p
    · have term := contains_divNat (n:=n+1) (contains_mul p ha)
      change (((taylor a n).2.mul a).divNat (n+1)).Contains _
      rw [show x^(n+1)/((n+1).factorial:ℝ)=x^n/(n.factorial:ℝ)*x/((n+1:ℕ):ℝ) by
        rw [pow_succ,Nat.factorial_succ,Nat.cast_mul];ring]
      exact term

theorem contains_squareN {a : Grid} {x : ℝ} (ha : a.Contains x) (n : ℕ) :
    (squareN a n).Contains (x^(2^n)) := by
  induction n with
  | zero => simpa only [squareN,pow_zero,pow_one] using ha
  | succ n ih =>
    simpa only [squareN,pow_succ 2 n,pow_mul,sq] using contains_mul ih ih

private theorem grid_taylor_error {x : ℝ} (small : |x|≤1/4) :
    (⟨-32,32,true⟩ : Grid).Contains (Real.exp x-expPolynomial 16 x) := by
  have ratio : |x|/(16+1)≤1/2 := by linarith
  have err := exp_polynomial_error (n:=16) (by norm_num at ratio ⊢;exact ratio)
  have pow := pow_le_pow_left₀ (abs_nonneg x) small 16
  have bound : |Real.exp x-expPolynomial 16 x| ≤ 32/(denom:ℝ) := by
    refine err.trans ?_
    calc _ ≤ (1/4:ℝ)^16/(Nat.factorial 16:ℝ)*2 := by gcongr
         _ ≤ _ := by norm_num [denom,Nat.factorial]
  intro _
  have h := abs_le.mp bound
  change ((-32:ℤ):ℝ)≤(denom:ℝ)*_ ∧ (denom:ℝ)*_≤((32:ℤ):ℝ)
  norm_num only [Int.cast_neg,Int.cast_ofNat]
  constructor
  · have l := (div_le_iff₀ real_denom_pos).mp (show -32/(denom:ℝ)≤Real.exp x-expPolynomial 16 x by simpa only [neg_div] using h.1)
    linarith
  · have u := (le_div_iff₀ real_denom_pos).mp h.2
    linarith

theorem contains_expPoint (a : ℤ) (hl : -16*denom≤a) (hu : a≤16*denom) :
    (expPoint a).Contains (Real.exp ((a:ℝ)/denom)) := by
  let x := (a:ℝ)/(denom:ℝ)/64
  let raw : Grid := ⟨a,a,decide (-16*denom≤a ∧ a≤16*denom)⟩
  have base : raw.Contains ((a:ℝ)/(denom:ℝ)) := by
    intro _
    change (a:ℝ)≤(denom:ℝ)*((a:ℝ)/denom) ∧ (denom:ℝ)*((a:ℝ)/denom)≤(a:ℝ)
    rw [show (denom:ℝ)*((a:ℝ)/denom)=(a:ℝ) by field_simp [real_denom_pos.ne']]
    exact ⟨le_rfl,le_rfl⟩
  have small : |x|≤1/4 := by
    apply abs_le.mpr
    have l : -(16:ℝ)*(denom:ℝ)≤(a:ℝ) := by exact_mod_cast hl
    have u : (a:ℝ)≤16*(denom:ℝ) := by exact_mod_cast hu
    dsimp [x]
    constructor
    · have k := (le_div_iff₀ real_denom_pos).mpr l
      linarith
    · have k := (div_le_iff₀ real_denom_pos).mpr u
      linarith
  have val : (raw.divNat 64).Contains x := contains_divNat base
  have poly := (contains_taylor val 16).1
  have mid := contains_add poly (grid_taylor_error small)
  rw [add_sub_cancel] at mid
  have sqr := contains_squareN mid 6
  change (expPoint a).Contains ((Real.exp x)^(2^6:ℕ)) at sqr
  rw [← Real.exp_nat_mul] at sqr
  convert sqr using 1
  congr 1
  dsimp [x]
  ring

theorem contains_exp {a : Grid} {x : ℝ} (ha : a.Contains x) : a.exp.Contains (Real.exp x) := by
  intro yes
  change ((a.ok && (expPoint a.lo).ok && (expPoint a.hi).ok) && decide (-16*denom≤a.lo ∧ a.hi≤16*denom))=true at yes
  simp only [Bool.and_eq_true,decide_eq_true_eq] at yes
  obtain ⟨⟨⟨ok,l⟩,u⟩,hl,hu⟩ := yes
  obtain ⟨L,U⟩ := ha ok
  have order : a.lo≤a.hi := by exact_mod_cast L.trans U
  have low := (contains_expPoint _ hl (order.trans hu) l).1
  have high := (contains_expPoint _ (hl.trans order) hu u).2
  refine ⟨low.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) real_denom_pos.le),
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) real_denom_pos.le).trans high⟩
  · exact (div_le_iff₀ real_denom_pos).mpr (by linarith)
  · exact (le_div_iff₀ real_denom_pos).mpr (by linarith)

end TwoAxisHelicoid.PdfVertical.Grid
#print axioms TwoAxisHelicoid.PdfVertical.Grid.contains_exp

