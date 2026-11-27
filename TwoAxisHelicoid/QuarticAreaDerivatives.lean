import TwoAxisHelicoid.ConformalAreaVariation

namespace TwoAxisHelicoid
open Real

noncomputable def areaQuarticDD (A B C s : ℝ) : ℝ := 2*A+6*B*s+12*C*s^2
noncomputable def quarticAreaD (g A B C s : ℝ) : ℝ :=
  areaQuarticD A B C s/(2*Real.sqrt (areaQuartic g A B C s))
noncomputable def quarticAreaDD (g A B C s : ℝ) : ℝ :=
  areaQuarticDD A B C s/(2*Real.sqrt (areaQuartic g A B C s))-
    (areaQuarticD A B C s)^2/(4*(Real.sqrt (areaQuartic g A B C s))^3)

theorem areaQuarticD_hasDerivAt (A B C s : ℝ) :
    HasDerivAt (areaQuarticD A B C) (areaQuarticDD A B C s) s := by
  have hd := HasDerivAt.add (HasDerivAt.add ((hasDerivAt_id s).const_mul (2*A))
    (((hasDerivAt_id s).pow 2).const_mul (3*B)))
      (((hasDerivAt_id s).pow 3).const_mul (4*C))
  convert hd using 1
  · rfl
  · unfold areaQuarticDD
    simp only [id_eq]
    ring

theorem quarticArea_hasDerivAt {g A B C s : ℝ} (hq : 0 < areaQuartic g A B C s) :
    HasDerivAt (fun s => Real.sqrt (areaQuartic g A B C s)) (quarticAreaD g A B C s) s :=
  (areaQuartic_hasDerivAt g A B C s).sqrt hq.ne'

theorem quarticAreaD_hasDerivAt {g A B C s : ℝ} (hq : 0 < areaQuartic g A B C s) :
    HasDerivAt (quarticAreaD g A B C) (quarticAreaDD g A B C s) s := by
  have hr : Real.sqrt (areaQuartic g A B C s) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hd := (areaQuarticD_hasDerivAt A B C s).div
    ((quarticArea_hasDerivAt hq).const_mul 2) (mul_ne_zero (by norm_num) hr)
  convert hd using 1
  · rfl
  · unfold quarticAreaDD quarticAreaD
    field_simp [hr]
    ring

theorem quarticAreaDD_zero {g : ℝ} (hg : 0 < g) (A B C : ℝ) :
    quarticAreaDD g A B C 0 = A/g := by
  simp [quarticAreaDD,areaQuarticDD,areaQuarticD,areaQuartic,Real.sqrt_sq hg.le]
  field_simp

/-- A uniform positive interval for the actual quartic Gram determinant.
Its coefficients may vary on a compact spatial patch. -/
theorem areaQuartic_pos_small {g A B C M s : ℝ} (hg : 1 ≤ g) (hM : 0 ≤ M)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hC : |C| ≤ M)
    (hs : |s| ≤ min 1 (1/(6*M+1))) : 0 < areaQuartic g A B C s := by
  have hs1 : |s| ≤ 1 := hs.trans (min_le_left _ _)
  have hs2 : |s| ≤ 1/(6*M+1) := hs.trans (min_le_right _ _)
  have h2 : |s|^2 ≤ |s| := by nlinarith [abs_nonneg s]
  have h3 : |s|^3 ≤ |s| := by
    have hm := mul_le_mul_of_nonneg_right h2 (abs_nonneg s)
    nlinarith
  have h4 : |s|^4 ≤ |s| := by
    have hm := mul_le_mul_of_nonneg_right h3 (abs_nonneg s)
    nlinarith
  have hAT : |A*s^2| ≤ M*|s| := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul hA h2 (by positivity) hM
  have hBT : |B*s^3| ≤ M*|s| := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul hB h3 (by positivity) hM
  have hCT : |C*s^4| ≤ M*|s| := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul hC h4 (by positivity) hM
  have hden : 0 < 6*M+1 := by positivity
  have hbound := (le_div_iff₀ hden).mp hs2
  have hAlow := (abs_le.mp hAT).1
  have hBlow := (abs_le.mp hBT).1
  have hClow := (abs_le.mp hCT).1
  unfold areaQuartic
  nlinarith [abs_nonneg s]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.areaQuartic_pos_small
