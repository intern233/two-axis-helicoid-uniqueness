import TwoAxisHelicoid.JacobiSmallRootBounds

namespace TwoAxisHelicoid
set_option maxHeartbeats 800000

noncomputable def jacobiRootRemainder (q r : ℝ) : ℝ :=
  jacobiGeometricSeries (-q^2) (-q^2*r)+jacobiGeometricSeries (-q^2) (q^4/r)

theorem jacobi_root_basic_bounds {q r : ℝ}
    (hq0 : 0 < q) (hrl : q/2 ≤ r) (hru : r ≤ q) :
    0 < r ∧ q ≤ q^2/r ∧ q^2/r ≤ 2*q := by
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrl
  refine ⟨hr, (le_div_iff₀ hr).mpr ?_, (div_le_iff₀ hr).mpr ?_⟩
  · nlinarith
  · nlinarith

theorem jacobiRootRemainder_abs_lt {q r : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100)
    (hrl : q/2 ≤ r) (hru : r ≤ q) : |jacobiRootRemainder q r| < 4*q^3 := by
  obtain ⟨hr, _, _⟩ := jacobi_root_basic_bounds hq0 hrl hru
  have h2 : q^2 ≤ 1/10000 := by
    convert pow_le_pow_left₀ hq0.le hq 2 using 1
    norm_num
  have h3 : q^3 ≤ 1/1000000 := by
    convert pow_le_pow_left₀ hq0.le hq 3 using 1
    norm_num
  have hQ : |-q^2| < 1 := by rw [abs_neg, abs_sq]; linarith
  have hcap : 2*q^3 < 1 := by linarith
  have hA : q^2*r ≤ q^3 := by nlinarith
  have hB : q^4/r ≤ 2*q^3 := by
    apply (div_le_iff₀ hr).mpr
    have hm := mul_le_mul_of_nonneg_left hrl (by positivity : 0 ≤ 2*q^3)
    nlinarith
  have habsA : |-q^2*r| = q^2*r := by
    rw [abs_mul, abs_neg, abs_sq, abs_of_pos hr]
  have habsB : |q^4/r| = q^4/r := abs_of_pos (by positivity)
  have hbA := jacobiGeometricSeries_abs_le_cap hQ hcap
    (habsA.le.trans (hA.trans (by nlinarith [pow_pos hq0 3])))
  have hbB := jacobiGeometricSeries_abs_le_cap hQ hcap (habsB.le.trans hB)
  rw [habsA, abs_neg, abs_sq] at hbA
  rw [habsB, abs_neg, abs_sq] at hbB
  let D := (1-q^2)*(1-2*q^3)^2
  have hDpos : 0 < D := mul_pos (by linarith) (sq_pos_of_pos (by linarith))
  have hD : (3/4 : ℝ) < D := by
    have hfirst : (99/100 : ℝ) ≤ 1-q^2 := by linarith
    have hsecond : (99/100 : ℝ) ≤ 1-2*q^3 := by linarith
    have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 99/100) hsecond 2
    have hprod := mul_le_mul hfirst hsquare (by norm_num : 0 ≤ (99/100 : ℝ)^2)
      (by linarith : 0 ≤ 1-q^2)
    dsimp only [D]
    norm_num at hprod
    linarith
  have hfinal : (q^2*r+q^4/r)/D < 4*q^3 := by
    apply (div_lt_iff₀ hDpos).mpr
    have hm := mul_lt_mul_of_pos_left hD (by positivity : 0 < 4*q^3)
    linarith
  calc
    _ ≤ |jacobiGeometricSeries (-q^2) (-q^2*r)|+|jacobiGeometricSeries (-q^2) (q^4/r)| := abs_add_le _ _
    _ ≤ (q^2*r)/D+(q^4/r)/D := add_le_add hbA hbB
    _ = (q^2*r+q^4/r)/D := by ring
    _ < _ := hfinal

theorem jacobiRealE_split_root {q r : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100)
    (hrl : q/2 ≤ r) (hru : r ≤ q) :
    jacobiRealE (-q^2) r = jacobiFraction r-
      (q^2/r)/(1+q^2/r)^2+jacobiRootRemainder q r := by
  obtain ⟨hr, _, hb⟩ := jacobi_root_basic_bounds hq0 hrl hru
  have hQ : |-q^2| < 1 := by rw [abs_neg, abs_sq]; nlinarith
  have ha : |-q^2/r| < 1 := by
    rw [abs_div, abs_neg, abs_sq, abs_of_pos hr]
    linarith
  unfold jacobiRealE jacobiRootRemainder
  rw [jacobiGeometricSeries_split hQ ha]
  rw [show -q^2*(-q^2/r) = q^4/r by ring]
  unfold jacobiFraction
  rw [show 1-(-q^2/r) = 1+q^2/r by ring]
  ring

theorem jacobi_beta_fraction_error_le {b : ℝ} (hb : 0 ≤ b) :
    b-b/(1+b)^2 ≤ 2*b^2 := by
  have hd : 0 < (1+b)^2 := sq_pos_of_pos (by linarith)
  have he : b-b/(1+b)^2 = b^2*(2+b)/(1+b)^2 := by field_simp; ring
  rw [he]
  apply (div_le_iff₀ hd).mpr
  nlinarith [pow_nonneg hb 3, pow_nonneg hb 4]

theorem jacobi_r_fraction_error_le {r : ℝ} (_hr : 0 ≤ r) (hru : r ≤ 1/100) :
    jacobiFraction r-r ≤ 3*r^2 := by
  have hd : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
  have he : jacobiFraction r-r = r^2*(2-r)/(1-r)^2 := by
    unfold jacobiFraction
    field_simp [show 1-r ≠ 0 by linarith]
    ring
  rw [he]
  apply (div_le_iff₀ hd).mpr
  have hc : 0 ≤ 1-5*r+3*r^2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg r) hc]

/-- The explicit balance bound used to control the left-end parameter kappa. -/
theorem jacobi_root_beta_sub_r_le {q r : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100)
    (hrl : q/2 ≤ r) (hru : r ≤ q) (hroot : jacobiRealE (-q^2) r = 0) :
    0 ≤ q^2/r-r ∧ q^2/r-r ≤ 12*q^2 := by
  obtain ⟨hr, hbl, hbu⟩ := jacobi_root_basic_bounds hq0 hrl hru
  refine ⟨by linarith, ?_⟩
  have he := jacobiRealE_split_root hq0 hq hrl hru
  rw [hroot] at he
  have hT := (le_abs_self _).trans (jacobiRootRemainder_abs_lt hq0 hq hrl hru).le
  have hbeta := jacobi_beta_fraction_error_le (hq0.le.trans hbl)
  have hrr := jacobi_r_fraction_error_le hr.le (hru.trans hq)
  have hb2 := pow_le_pow_left₀ (hq0.le.trans hbl) hbu 2
  have hr2 := pow_le_pow_left₀ hr.le hru 2
  have hq3 := mul_le_mul_of_nonneg_left (show q ≤ (1/4 : ℝ) by linarith) (sq_nonneg q)
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiRootRemainder_abs_lt
#print axioms TwoAxisHelicoid.jacobi_root_beta_sub_r_le
