import TwoAxisHelicoid.PdfVerticalGrid
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace TwoAxisHelicoid.PdfVertical.Grid

/-- Every accepted interval contains its value after scaling by 2^80. -/
def Contains (a : Grid) (x : ℝ) : Prop :=
  a.ok=true → (a.lo:ℝ)≤(denom:ℝ)*x ∧ (denom:ℝ)*x≤(a.hi:ℝ)

theorem denom_pos : (0:ℤ)<denom := by decide
theorem real_denom_pos : (0:ℝ)<(denom:ℝ) := by exact_mod_cast denom_pos

theorem floor_ratio_le (a b : ℤ) (hb : 0<b) : ((a/b:ℤ):ℝ)≤(a:ℝ)/b := by
  apply (le_div_iff₀ (by exact_mod_cast hb : (0:ℝ)<b)).mpr
  exact_mod_cast Int.ediv_mul_le a hb.ne'

theorem le_ceil_ratio (a b : ℤ) (hb : 0<b) : (a:ℝ)/b≤((-((-a)/b):ℤ):ℝ) := by
  have h := floor_ratio_le (-a) b hb
  rw [Int.cast_neg,neg_div] at h
  rw [Int.cast_neg]
  linarith only [h]

theorem contains_int (n : ℤ) : (ofInt n).Contains (n:ℝ) := by
  intro _
  simp [ofInt,mul_comm]

theorem contains_rats {a b : ℚ} {x : ℝ} (ha : (a:ℝ)≤x) (hb : x≤(b:ℝ)) :
    (ofRats a b).Contains x := by
  intro _
  have val (q : ℚ) : ((q.num*denom:ℤ):ℝ)/(q.den:ℝ)=(denom:ℝ)*(q:ℝ) := by
    rw [Rat.cast_def q,Int.cast_mul]
    ring
  constructor
  · apply (floor_ratio_le _ (a.den:ℤ) (by exact_mod_cast a.den_pos)).trans
    change ((a.num*denom:ℤ):ℝ)/(a.den:ℝ)≤_
    rw [val]
    exact mul_le_mul_of_nonneg_left ha real_denom_pos.le
  · apply (mul_le_mul_of_nonneg_left hb real_denom_pos.le).trans
    rw [← val b]
    simpa only [ofRats,Int.cast_natCast,neg_mul] using
      le_ceil_ratio (b.num*denom) (b.den:ℤ) (by exact_mod_cast b.den_pos)

theorem contains_add {a b : Grid} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.add b).Contains (x+y) := by
  intro yes
  have flags := Bool.and_eq_true_iff.mp yes
  obtain ⟨l,r⟩ := ha flags.1
  obtain ⟨s,t⟩ := hb flags.2
  change ((a.lo+b.lo:ℤ):ℝ)≤_ ∧ _≤((a.hi+b.hi:ℤ):ℝ)
  rw [Int.cast_add,Int.cast_add,mul_add]
  exact ⟨add_le_add l s,add_le_add r t⟩

theorem contains_neg {a : Grid} {x : ℝ} (ha : a.Contains x) : a.neg.Contains (-x) := by
  intro yes
  have h := ha yes
  change ((-a.hi:ℤ):ℝ)≤_ ∧ _≤((-a.lo:ℤ):ℝ)
  simp only [Int.cast_neg,mul_neg,neg_le_neg_iff]
  exact ⟨h.2,h.1⟩

theorem contains_sub {a b : Grid} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.sub b).Contains (x-y) := contains_add ha (contains_neg hb)

private theorem scaled_between {a b y : ℝ} (h : a≤y ∧ y≤b) (k : ℝ) :
    min (k*a) (k*b)≤k*y ∧ k*y≤max (k*a) (k*b) := by
  rcases le_total 0 k with pos|neg
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h.1 pos),
      (mul_le_mul_of_nonneg_left h.2 pos).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h.2 neg),
      (mul_le_mul_of_nonpos_left h.1 neg).trans (le_max_left _ _)⟩

theorem contains_mul {a b : Grid} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.mul b).Contains (x*y) := by
  intro yes
  have flags := Bool.and_eq_true_iff.mp yes
  let D := (denom:ℝ)
  have A := ha flags.1
  have B := hb flags.2
  let m := min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
  let M := max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))
  have left := scaled_between B (a.lo:ℝ)
  have right := scaled_between B (a.hi:ℝ)
  have mid := scaled_between A (D*y)
  have lower : (m:ℝ)≤(D*x)*(D*y) := by
    dsimp only [m]
    push_cast
    rw [mul_comm (D*x)]
    apply le_trans _ mid.1
    exact le_min ((min_le_left _ _).trans (left.1.trans_eq (mul_comm _ _)))
      ((min_le_right _ _).trans (right.1.trans_eq (mul_comm _ _)))
  have upper : (D*x)*(D*y)≤(M:ℝ) := by
    dsimp only [M]
    push_cast
    rw [mul_comm (D*x)]
    apply mid.2.trans
    exact max_le (((mul_comm _ _).le.trans left.2).trans (le_max_left _ _))
      (((mul_comm _ _).le.trans right.2).trans (le_max_right _ _))
  have clean : (D*x)*(D*y)/D=D*(x*y) := by field_simp [show D≠0 from real_denom_pos.ne']
  change ((m/denom:ℤ):ℝ)≤D*(x*y) ∧ D*(x*y)≤((-((-M)/denom):ℤ):ℝ)
  rw [← clean]
  exact ⟨(floor_ratio_le _ _ denom_pos).trans (div_le_div_of_nonneg_right lower real_denom_pos.le),
    (div_le_div_of_nonneg_right upper real_denom_pos.le).trans (le_ceil_ratio _ _ denom_pos)⟩

theorem contains_inv {a : Grid} {x : ℝ} (ha : a.Contains x) : a.invPos.Contains x⁻¹ := by
  intro yes
  obtain ⟨ok,pos⟩ := Bool.and_eq_true_iff.mp yes
  have low : (0:ℝ)<(a.lo:ℝ) := by exact_mod_cast (of_decide_eq_true pos : 0<a.lo)
  have h := ha ok
  have dx := low.trans_le h.1
  have ux := dx.trans_le h.2
  have xp : 0<x := pos_of_mul_pos_right dx real_denom_pos.le
  change (((denom*denom)/a.hi:ℤ):ℝ)≤_ ∧ _≤((-((-(denom*denom))/a.lo):ℤ):ℝ)
  constructor
  · apply (floor_ratio_le _ _ (by exact_mod_cast ux)).trans
    rw [Int.cast_mul,le_mul_inv_iff₀ xp,div_mul_eq_mul_div,div_le_iff₀ ux]
    nlinarith only [mul_le_mul_of_nonneg_left h.2 real_denom_pos.le]
  · apply le_trans _ (le_ceil_ratio _ _ (by exact_mod_cast low))
    rw [Int.cast_mul,le_div_iff₀ low]
    apply (mul_le_mul_iff_left₀ xp).mp
    field_simp [xp.ne']
    nlinarith only [mul_le_mul_of_nonneg_left h.1 real_denom_pos.le]

theorem contains_div {a b : Grid} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (a.divPos b).Contains (x/y) := by simpa only [divPos,div_eq_mul_inv] using contains_mul ha (contains_inv hb)

theorem contains_divNat {a : Grid} {x : ℝ} (ha : a.Contains x) {n : ℕ} :
    (a.divNat n).Contains (x/(n:ℝ)) := by
  intro yes
  obtain ⟨ok,nz⟩ := Bool.and_eq_true_iff.mp yes
  have np : 0<n := Nat.pos_of_ne_zero (of_decide_eq_true nz)
  have h := ha ok
  have ip : (0:ℤ)<(n:ℤ) := by exact_mod_cast np
  have rp : (0:ℝ)<(n:ℝ) := by exact_mod_cast np
  change ((a.lo/(n:ℤ):ℤ):ℝ)≤_ ∧ _≤((-((-a.hi)/(n:ℤ)):ℤ):ℝ)
  rw [← mul_div_assoc]
  simpa only [Int.cast_natCast] using And.intro
    ((floor_ratio_le _ _ ip).trans (div_le_div_of_nonneg_right h.1 rp.le))
    ((div_le_div_of_nonneg_right h.2 rp.le).trans (le_ceil_ratio _ _ ip))

theorem contains_pi : pi.Contains Real.pi := by
  apply contains_rats
  · have h := Real.pi_gt_d20.le
    norm_num at h ⊢
    exact h
  · have h := Real.pi_lt_d20.le
    norm_num at h ⊢
    exact h

end TwoAxisHelicoid.PdfVertical.Grid
#print axioms TwoAxisHelicoid.PdfVertical.Grid.contains_mul
#print axioms TwoAxisHelicoid.PdfVertical.Grid.contains_inv
