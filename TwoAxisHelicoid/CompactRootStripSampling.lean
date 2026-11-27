import TwoAxisHelicoid.PdfPrimalGridSampling
import TwoAxisHelicoid.PdfPrimalParameterBox

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

def CompactRootStripPiece (l u : ℚ) (t a : ℝ) : Prop :=
  ∀ z : ℂ, z.re∈Icc (l:ℝ) (u:ℝ) → |z.im|=5/16 →
    ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤10^6

theorem compact_root_strip_piece {T : Grid} {p : PrimalThetaParameters} {t a : ℝ}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t) (l u : ℚ)
    (checked : ∀ f : Bool, let y : ℚ := if f then 5/16 else -5/16
      let b := primalStripOutput T p l u y y
      b.ok=true ∧ b.mag≤10^6*Grid.denom) : CompactRootStripPiece l u t a := by
  intro z zx zy
  have edge : ∃ f : Bool, z.im=(((if f then 5/16 else -5/16 : ℚ)):ℝ) := by
    by_cases h : 0≤z.im
    · refine ⟨true,?_⟩
      rw [abs_of_nonneg h] at zy
      simpa only [ite_true,Rat.cast_div,Rat.cast_ofNat] using zy
    · refine ⟨false,?_⟩
      rw [abs_of_neg (lt_of_not_ge h)] at zy
      norm_num
      linarith
  obtain ⟨f,y⟩ := edge
  obtain ⟨ok,mag⟩ := checked f
  have val := primalStripOutput_contains ts ps ht zx ⟨y.ge,y.le⟩
  apply (CGrid.norm_le_mag val ok).trans
  rw [Grid.value,div_le_iff₀ Grid.real_denom_pos]
  exact_mod_cast mag

theorem CompactRootStripPiece.merge {l mid u : ℚ} {t a : ℝ}
    (left : CompactRootStripPiece l mid t a) (right : CompactRootStripPiece mid u t a) :
    CompactRootStripPiece l u t a := by
  intro z x y
  by_cases low : z.re≤(mid:ℝ)
  · exact left z ⟨x.1,low⟩ y
  · exact right z ⟨le_of_lt (lt_of_not_ge low),x.2⟩ y

theorem compact_root_trapezoidal_error :
    let r := Real.exp (-(2*Real.pi*((32:ℝ)*(5/16))))
    2*((10^6:ℝ)*r/(1-r))≤1/10^20 := by
  let r := Real.exp (-(2*Real.pi*((32:ℝ)*(5/16))))
  have exp62 : (27/10:ℝ)^62≤Real.exp 62 := by
    rw [show (62:ℝ)=(62:ℕ)*(1:ℝ) by norm_num,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have up : r≤1/(27/10:ℝ)^62 := by
    dsimp only [r]
    simp only [Real.exp_neg,one_div]
    exact inv_anti₀ (by positivity) (exp62.trans (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_d2])))
  change 2*((10^6:ℝ)*r/(1-r))≤_
  have tiny : r≤3/10^27 := up.trans (by norm_num)
  have den : 0<1-r := by linarith
  rw [← mul_div_assoc,div_le_iff₀ den]
  linarith

theorem compact_root_theta_sampling {t a : ℝ} (ht : 17/20≤t) (strip : CompactRootStripPiece (-1) 0 t a) :
    |(1/32:ℝ)*(∑ k∈Finset.range 32,
      (thetaA t a (((-1+(k:ℝ)/32:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)-thetaHorizontalPeriod t a|≤1/10^20 := by
  have h := periodic_theta_sample_error (N:=32) (by decide) (s:=5/16) (by norm_num)
    (by linarith : 2*(5/16)<t) (by simpa only [CompactRootStripPiece,Rat.cast_neg,Rat.cast_one,Rat.cast_zero] using strip)
  exact h.trans compact_root_trapezoidal_error

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compact_root_theta_sampling
