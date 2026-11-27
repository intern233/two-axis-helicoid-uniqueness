import TwoAxisHelicoid.JacobiRealSeries

namespace TwoAxisHelicoid
set_option maxHeartbeats 800000

theorem jacobiGeometricSeries_abs_le_cap {Q a r : ℝ}
    (hQ : |Q| < 1) (hr : r < 1) (ha : |a| ≤ r) :
    |jacobiGeometricSeries Q a| ≤ |a|/((1-|Q|)*(1-r)^2) := by
  have ha1 := ha.trans_lt hr
  apply (jacobiGeometricSeries_abs_le hQ ha1).trans
  apply div_le_div_of_nonneg_left (abs_nonneg a)
    (mul_pos (sub_pos.mpr hQ) (sq_pos_of_pos (sub_pos.mpr hr)))
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sub_pos.mpr hr).le (sub_le_sub_left ha 1) 2) (sub_pos.mpr hQ).le

theorem jacobi_small_tail_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100) :
    |jacobiGeometricSeries (-q^2) (q^5/2)+jacobiGeometricSeries (-q^2) (2*q^3)| < 3*q^3 := by
  have h2 : q^2 ≤ 1/10000 := by
    convert pow_le_pow_left₀ hq0.le hq 2 using 1
    norm_num
  have h3 : q^3 ≤ 1/1000000 := by
    convert pow_le_pow_left₀ hq0.le hq 3 using 1
    norm_num
  have hQ : |-q^2| < 1 := by rw [abs_neg, abs_sq]; linarith
  have hr : 2*q^3 < 1 := by linarith
  have ha : |q^5/2| ≤ 2*q^3 := by
    rw [abs_of_pos (by positivity)]
    calc
      _ = q^3*(q^2/2) := by ring
      _ ≤ q^3*2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hA := jacobiGeometricSeries_abs_le_cap hQ hr ha
  have hB := jacobiGeometricSeries_abs_le_cap hQ hr
    (le_of_eq (abs_of_pos (by positivity : 0 < 2*q^3)))
  rw [abs_of_pos (by positivity : 0 < 2*q^3)] at hB
  simp only [abs_neg, abs_sq, abs_of_pos (by positivity : 0 < q^5/2)] at hA
  simp only [abs_neg, abs_sq] at hB
  let D := (1-q^2)*(1-2*q^3)^2
  have hDpos : 0 < D := mul_pos (by linarith) (sq_pos_of_pos (by linarith))
  have hD : (3/4 : ℝ) < D := by
    have hfirst : (99/100 : ℝ) ≤ 1-q^2 := by linarith
    have hsecond : (99/100 : ℝ) ≤ 1-2*q^3 := by linarith
    have hsquare : (99/100 : ℝ)^2 ≤ (1-2*q^3)^2 :=
      pow_le_pow_left₀ (by norm_num) hsecond 2
    have hprod := mul_le_mul hfirst hsquare (by norm_num : 0 ≤ (99/100 : ℝ)^2)
      (by linarith : 0 ≤ 1-q^2)
    dsimp only [D]
    norm_num at hprod
    linarith
  have hnum : q^5/2+2*q^3 ≤ (9/4)*q^3 := by
    calc
      _ = q^3*(q^2/2+2) := by ring
      _ ≤ q^3*(9/4) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hfrac : (q^5/2+2*q^3)/D < 3*q^3 := by
    apply (div_lt_iff₀ hDpos).mpr
    have hm := mul_lt_mul_of_pos_left hD (by positivity : 0 < 3*q^3)
    nlinarith
  calc
    _ ≤ |jacobiGeometricSeries (-q^2) (q^5/2)|+|jacobiGeometricSeries (-q^2) (2*q^3)| := abs_add_le _ _
    _ ≤ (q^5/2)/D+(2*q^3)/D := add_le_add hA hB
    _ = (q^5/2+2*q^3)/D := by ring
    _ < _ := hfrac

theorem jacobiFraction_half_q_lt {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100) :
    jacobiFraction (q/2) < (3/5)*q := by
  have hs : (5/6 : ℝ) < (1-q/2)^2 := by nlinarith
  unfold jacobiFraction
  apply (div_lt_iff₀ (sq_pos_of_pos (by linarith : 0 < 1-q/2))).mpr
  have hm := mul_lt_mul_of_pos_left hs hq0
  nlinarith

theorem jacobiFraction_neg_two_q_lt {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100) :
    jacobiFraction (-2*q) < -(19/10)*q := by
  have hs : (1+2*q)^2 < (20/19 : ℝ) := by nlinarith
  unfold jacobiFraction
  rw [show 1-(-2*q) = 1+2*q by ring]
  apply (div_lt_iff₀ (sq_pos_of_pos (by positivity : 0 < 1+2*q))).mpr
  have hm := mul_lt_mul_of_pos_left hs hq0
  nlinarith

/-- The explicit upper-root test from manuscript Lemma 7.2. -/
theorem jacobiRealE_half_q_lt_neg_q {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100) :
    jacobiRealE (-q^2) (q/2) < -q := by
  have h2 : q^2 ≤ 1/10000 := by
    convert pow_le_pow_left₀ hq0.le hq 2 using 1
    norm_num
  have h3 : q^3 ≤ 1/1000000 := by
    convert pow_le_pow_left₀ hq0.le hq 3 using 1
    norm_num
  have hQ : |-q^2| < 1 := by rw [abs_neg, abs_sq]; linarith
  have ha : |(-q^3/2)| < 1 := by
    rw [abs_of_neg (by nlinarith [pow_pos hq0 3])]
    linarith
  have hb : |(-2*q)| < 1 := by
    rw [abs_of_neg (by nlinarith)]
    linarith
  have hsplit : jacobiRealE (-q^2) (q/2) =
      jacobiFraction (q/2)+jacobiFraction (-q^3/2)+jacobiFraction (-2*q)+
        (jacobiGeometricSeries (-q^2) (q^5/2)+jacobiGeometricSeries (-q^2) (2*q^3)) := by
    unfold jacobiRealE
    rw [show -q^2*(q/2) = -q^3/2 by ring,
      show -q^2/(q/2) = -2*q by field_simp]
    rw [jacobiGeometricSeries_split hQ ha, jacobiGeometricSeries_split hQ hb]
    rw [show -q^2*(-q^3/2) = q^5/2 by ring, show -q^2*(-2*q) = 2*q^3 by ring]
    ring
  have hn : jacobiFraction (-q^3/2) < 0 := by
    unfold jacobiFraction
    exact div_neg_of_neg_of_pos (by nlinarith [pow_pos hq0 3])
      (sq_pos_of_pos (by nlinarith [pow_pos hq0 3]))
  have htail := (le_abs_self _).trans_lt (jacobi_small_tail_bound hq0 hq)
  have hsmall : 3*q^3 ≤ (3/10000)*q := by
    have hm := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 3*q)
    nlinarith
  rw [hsplit]
  have hpos := jacobiFraction_half_q_lt hq0 hq
  have hneg := jacobiFraction_neg_two_q_lt hq0 hq
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobi_small_tail_bound
#print axioms TwoAxisHelicoid.jacobiRealE_half_q_lt_neg_q
