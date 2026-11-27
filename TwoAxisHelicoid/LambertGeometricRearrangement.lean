import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

namespace TwoAxisHelicoid

/-- Exchange the two positive-integer indices in a geometrically
damped Lambert series. Absolute summability is proved on the product
before either iteration of the sum. Powers zero and one give the
logarithmic product and its derivative used in Sections 5 and 8. -/
theorem geometric_lambert_rearrangement {K : Type*} [RCLike K] (p : ℕ) {Q u : K}
    (hQ : ‖Q‖<1) (hu : ‖u‖<1) :
    let term := fun n : ℕ => ((n+1:ℕ):K)^p*u^(n+1)/(1-Q^(n+1))
    Summable term ∧
      (∑' m : ℕ, ∑' n : ℕ, ((n+1:ℕ):K)^p*(Q^m*u)^(n+1))=∑' n, term n := by
  let b := fun (m n : ℕ) => ((n+1:ℕ):K)^p*(Q^m*u)^(n+1)
  let W := fun n : ℕ => ((n+1:ℕ):ℝ)^p*‖u‖^(n+1)
  have base : Summable (fun n : ℕ => (n:ℝ)^p*‖u‖^n) :=
    summable_pow_mul_geometric_of_norm_lt_one (r := ‖u‖) p (by simpa only [Real.norm_eq_abs, abs_norm] using hu)
  have sW : Summable W := (summable_nat_add_iff 1).mpr base
  have major := (summable_geometric_of_lt_one (norm_nonneg Q) hQ).mul_of_nonneg sW
    (fun m => pow_nonneg (norm_nonneg Q) m) (fun n => by dsimp [W]; positivity)
  have total : Summable (Function.uncurry b) := by
    apply Summable.of_norm_bounded major
    rintro ⟨m,n⟩
    dsimp only [Function.uncurry,b,W]
    rw [norm_mul,norm_pow,norm_pow,norm_mul,norm_pow]
    have normCast : ‖((n+1:ℕ):K)‖=((n+1:ℕ):ℝ) := RCLike.norm_natCast _
    rw [normCast,mul_pow]
    have dec := pow_le_of_le_one (pow_nonneg (norm_nonneg Q) m) (pow_le_one₀ (norm_nonneg Q) hQ.le) (Nat.succ_ne_zero n)
    calc _ ≤ ((n+1:ℕ):ℝ)^p*(‖Q‖^m*‖u‖^(n+1)) := by gcongr
         _ = _ := by ring
  have column (n : ℕ) : (∑' m : ℕ, b m n)=((n+1:ℕ):K)^p*u^(n+1)/(1-Q^(n+1)) := by
    have reg : ‖Q^(n+1)‖<1 := by rw [norm_pow];exact pow_lt_one₀ (norm_nonneg Q) hQ (Nat.succ_ne_zero n)
    have term (m : ℕ) : b m n=(((n+1:ℕ):K)^p*u^(n+1))*(Q^(n+1))^m := by
      dsimp [b]
      rw [mul_pow,← pow_mul,← pow_mul,Nat.mul_comm m (n+1)]
      ring
    rw [tsum_congr term,tsum_mul_left,tsum_geometric_of_norm_lt_one reg,div_eq_mul_inv]
  refine ⟨total.prod_symm.prod.congr column,?_⟩
  exact total.tsum_comm.symm.trans (tsum_congr column)

/-- The original unweighted logarithmic kernel and the differentiated
kernel both have closed Lambert expansions throughout the bidisk. -/
theorem geometric_lambert_orders_zero_one {K : Type*} [RCLike K] {Q u : K}
    (hQ : ‖Q‖<1) (hu : ‖u‖<1) :
    (Summable (fun n : ℕ => u^(n+1)/(1-Q^(n+1))) ∧
      (∑' m : ℕ, (Q^m*u)/(1-Q^m*u))=∑' n : ℕ, u^(n+1)/(1-Q^(n+1))) ∧
    (Summable (fun n : ℕ => ((n+1:ℕ):K)*u^(n+1)/(1-Q^(n+1))) ∧
      (∑' m : ℕ, (Q^m*u)/(1-Q^m*u)^2)=∑' n : ℕ, ((n+1:ℕ):K)*u^(n+1)/(1-Q^(n+1))) := by
  have reg (m : ℕ) : ‖Q^m*u‖<1 := by
    rw [norm_mul,norm_pow]
    exact ((mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg Q) hQ.le) (norm_nonneg u)).trans_eq (one_mul _)).trans_lt hu
  obtain ⟨sm0,h0⟩ := geometric_lambert_rearrangement 0 hQ hu
  obtain ⟨sm1,h1⟩ := geometric_lambert_rearrangement 1 hQ hu
  simp only [pow_zero,one_mul] at sm0 h0
  simp only [pow_one] at sm1 h1
  refine ⟨⟨sm0,Eq.trans (tsum_congr fun m => ?_) h0⟩,⟨sm1,Eq.trans (tsum_congr fun m => ?_) h1⟩⟩
  · rw [show (fun n : ℕ => (Q^m*u)^(n+1))=fun n => (Q^m*u)*(Q^m*u)^n from funext fun n => pow_succ' _ n,
      tsum_mul_left,tsum_geometric_of_norm_lt_one (reg m),div_eq_mul_inv]
  · have h := (hasSum_coe_mul_geometric_of_norm_lt_one (reg m)).summable.tsum_eq_zero_add
    simpa only [Nat.cast_zero,zero_mul,zero_add,tsum_coe_mul_geometric_of_norm_lt_one (reg m)] using h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.geometric_lambert_rearrangement
#print axioms TwoAxisHelicoid.geometric_lambert_orders_zero_one
