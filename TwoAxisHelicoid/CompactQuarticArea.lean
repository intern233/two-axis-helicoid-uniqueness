import TwoAxisHelicoid.QuarticAreaDerivatives
import TwoAxisHelicoid.CompactAreaVariation

namespace TwoAxisHelicoid
open Set MeasureTheory

/-- Uniform positivity and explicit derivatives justify differentiating
the compact-patch area integral twice, from continuous coefficient data. -/
theorem compact_quartic_area_integral_second_derivative
    {g A B C : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hgC : ContinuousOn g K) (hAC : ContinuousOn A K)
    (hBC : ContinuousOn B K) (hCC : ContinuousOn C K)
    (hg : ∀ p ∈ K, 1 ≤ g p) :
    HasDerivAt (deriv (fun s : ℝ => ∫ p in K,
      Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s))) (∫ p in K, A p/g p) 0 := by
  obtain ⟨MA,hMA⟩ := hK.exists_bound_of_continuousOn hAC
  obtain ⟨MB,hMB⟩ := hK.exists_bound_of_continuousOn hBC
  obtain ⟨MC,hMC⟩ := hK.exists_bound_of_continuousOn hCC
  let M := |MA|+|MB|+|MC|+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ha (p : ℝ × ℝ) (hp : p ∈ K) : |A p| ≤ M := by
    have h := hMA p hp
    simp only [Real.norm_eq_abs] at h
    dsimp [M]
    linarith [le_abs_self MA,abs_nonneg MB,abs_nonneg MC]
  have hb (p : ℝ × ℝ) (hp : p ∈ K) : |B p| ≤ M := by
    have h := hMB p hp
    simp only [Real.norm_eq_abs] at h
    dsimp [M]
    linarith [abs_nonneg MA,le_abs_self MB,abs_nonneg MC]
  have hc (p : ℝ × ℝ) (hp : p ∈ K) : |C p| ≤ M := by
    have h := hMC p hp
    simp only [Real.norm_eq_abs] at h
    dsimp [M]
    linarith [abs_nonneg MA,abs_nonneg MB,le_abs_self MC]
  let ε := min 1 (1/(6*M+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let S := Icc (-ε) ε ×ˢ K
  have hpos s (hs : s ∈ Icc (-ε) ε) p (hp : p ∈ K) :
      0 < areaQuartic (g p) (A p) (B p) (C p) s :=
    areaQuartic_pos_small (hg p hp) hM (ha p hp) (hb p hp) (hc p hp) (abs_le.mpr hs)
  have hgc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g q.2) S :=
    hgC.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hac : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => A q.2) S :=
    hAC.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hbc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => B q.2) S :=
    hBC.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hcc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => C q.2) S :=
    hCC.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hsc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => q.1) S := continuous_fst.continuousOn
  have hqc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      areaQuartic (g q.2) (A q.2) (B q.2) (C q.2) q.1) S :=
    (((hgc.pow 2).add (hac.mul (hsc.pow 2))).add (hbc.mul (hsc.pow 3))).add (hcc.mul (hsc.pow 4))
  have hqd : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      areaQuarticD (A q.2) (B q.2) (C q.2) q.1) S := by
    unfold areaQuarticD
    fun_prop
  have hqdd : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      areaQuarticDD (A q.2) (B q.2) (C q.2) q.1) S := by
    unfold areaQuarticDD
    fun_prop
  have hsqrt := Real.continuous_sqrt.comp_continuousOn hqc
  have hn q (hq : q ∈ S) : Real.sqrt (areaQuartic (g q.2) (A q.2) (B q.2) (C q.2) q.1) ≠ 0 :=
    (Real.sqrt_pos.mpr (hpos q.1 hq.1 q.2 hq.2)).ne'
  have hdc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      quarticAreaD (g q.2) (A q.2) (B q.2) (C q.2) q.1) S :=
    hqd.div (hsqrt.const_mul 2) (fun q hq => mul_ne_zero (by norm_num) (hn q hq))
  have hddc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      quarticAreaDD (g q.2) (A q.2) (B q.2) (C q.2) q.1) S :=
    (hqdd.div (hsqrt.const_mul 2) (fun q hq => mul_ne_zero (by norm_num) (hn q hq))).sub
      ((hqd.pow 2).div ((hsqrt.pow 3).const_mul 4)
        (fun q hq => mul_ne_zero (by norm_num) (pow_ne_zero _ (hn q hq))))
  have hd := second_derivative_compact_plane_integral hK
    (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨neg_lt_zero.mpr hε,hε⟩) hsqrt hdc hddc
    (fun s hs p hp => quarticArea_hasDerivAt (hpos s ⟨hs.1.le,hs.2.le⟩ p hp))
    (fun s hs p hp => quarticAreaD_hasDerivAt (hpos s ⟨hs.1.le,hs.2.le⟩ p hp))
  have hi : (∫ p in K, quarticAreaDD (g p) (A p) (B p) (C p) 0) = ∫ p in K, A p/g p := by
    apply setIntegral_congr_fun hK.measurableSet
    intro p hp
    exact quarticAreaDD_zero (lt_of_lt_of_le (by norm_num) (hg p hp)) _ _ _
  rw [hi] at hd
  exact hd

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_quartic_area_integral_second_derivative
