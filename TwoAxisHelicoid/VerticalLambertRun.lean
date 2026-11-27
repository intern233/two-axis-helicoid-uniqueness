import TwoAxisHelicoid.VerticalDecimalBoxes
import TwoAxisHelicoid.LambertTail

namespace TwoAxisHelicoid.VerticalAttachment

private theorem signedPower_contains {q : Box} {x : ℝ} (hx : ContainsReal q x)
    (hq : 0 ≤ q.1) (n : ℕ) : ContainsReal (signedPower q n) ((-x)^n) := by
  have hl : 0 ≤ (q.1 : ℝ) := by exact_mod_cast hq
  have p : ContainsReal (q.1^n, q.2^n) (x^n) := by
    simpa only [ContainsReal, Rat.cast_pow] using
      And.intro (pow_le_pow_left₀ hl hx.1 n) (pow_le_pow_left₀ (hl.trans hx.1) hx.2 n)
  by_cases h : n % 2 = 1
  · rw [signedPower, ite_eq_left h, (Nat.odd_iff.mpr h).neg_pow]
    exact boxNeg_contains p
  · have even : Even n := Nat.not_odd_iff_even.mp (fun ho => h (Nat.odd_iff.mp ho))
    rw [signedPower, ite_eq_right h, even.neg_pow]
    exact p

noncomputable def uploadedLambertTerm (x : ℝ) (p n : ℕ) : ℝ :=
  ((n+1 : ℕ) : ℝ)^p * (-x)^(n+1)/(1-(-x)^(n+1))

private theorem prefix_contains {x : ℝ} (hx : ContainsReal endpointNome x) (p n : ℕ)
    (hn : n ≤ 20) :
    ContainsReal (lambertPrefix endpointNome p n) (∑ k ∈ Finset.range n, uploadedLambertTerm x p k) := by
  induction n with
  | zero => simp [lambertPrefix, ContainsReal]
  | succ n ih =>
    have power := signedPower_contains hx (by decide +kernel) (n+1)
    have one : ContainsReal oneBox 1 := by simp [ContainsReal, oneBox]
    have den := boxAdd_contains one (boxNeg_contains power)
    have nonzero := (original_lambert_divisors_positive ⟨n, by omega⟩).1
    have frac := boxDiv_contains power den nonzero
    have scaled := boxScale_contains frac (((n+1)^p : ℕ) : ℚ)
    rw [lambertPrefix, Finset.sum_range_succ]
    apply boxAdd_contains (ih (by omega))
    simpa [uploadedLambertTerm, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using scaled

/-- The two 20-term runs, including the uploaded tail formula, enclose the
infinite real Lambert sums at every nome in the endpoint interval. -/
theorem original_lambert_real_sums {x : ℝ} (hx : ContainsReal endpointNome x) :
    ContainsReal endS1 (∑' n : ℕ, uploadedLambertTerm x 1 n) ∧
    ContainsReal endS3 (∑' n : ℕ, uploadedLambertTerm x 3 n) := by
  let b : ℝ := (endpointNome.2 : ℝ)
  have q0 : 0 ≤ (endpointNome.1 : ℝ) := by
    exact_mod_cast (show 0 ≤ endpointNome.1 by decide +kernel)
  have hb0 : 0 ≤ b := (q0.trans hx.1).trans hx.2
  have hb1 : b < 1 := by
    change (endpointNome.2 : ℝ) < 1
    exact_mod_cast (show endpointNome.2 < 1 by decide +kernel)
  have major : |-x| ≤ b := by rw [abs_neg, abs_of_nonneg (q0.trans hx.1)]; exact hx.2
  have result (p : ℕ) (err : ℚ) (h :
      |(∑' n : ℕ, uploadedLambertTerm x p n) - ∑ n ∈ Finset.range 20, uploadedLambertTerm x p n| ≤ (err : ℝ)) :
      ContainsReal (boxAdd (lambertPrefix endpointNome p 20) (-err,err))
        (∑' n : ℕ, uploadedLambertTerm x p n) := by
    let s := ∑' n : ℕ, uploadedLambertTerm x p n
    let c := ∑ n ∈ Finset.range 20, uploadedLambertTerm x p n
    have he : ContainsReal (-err,err) (s-c) := by
      simpa only [ContainsReal, Rat.cast_neg] using abs_le.mp h
    have glue : ContainsReal (boxAdd (lambertPrefix endpointNome p 20) (-err,err)) (c+(s-c)) :=
      boxAdd_contains (prefix_contains hx p 20 le_rfl) he
    rwa [show c+(s-c) = s by ring] at glue
  constructor
  · rw [← original_lambert_one]
    unfold lambertBox
    apply result
    simpa [uploadedLambertTerm, b, linearTail, Nat.cast_add, show (20:ℝ)+1 = 21 by norm_num,
      show (1:ℝ)+20 = 21 by norm_num] using
      lambert_linear_remainder_bound hb0 hb1 major 20
  · rw [← original_lambert_three]
    unfold lambertBox
    apply result
    simpa [uploadedLambertTerm, b, cubicTail, Nat.cast_add, pow_two, show (20:ℝ)+1 = 21 by norm_num] using
      lambert_cubic_remainder_bound hb0 hb1 major 20

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.original_lambert_real_sums
