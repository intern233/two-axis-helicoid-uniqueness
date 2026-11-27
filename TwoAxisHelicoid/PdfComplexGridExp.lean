import TwoAxisHelicoid.PdfComplexGridSound
import TwoAxisHelicoid.PdfVerticalGridExp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace TwoAxisHelicoid.PdfVertical.CGrid
open Complex

private theorem taylor_contains {a : CGrid} {z : ℂ} (h : a.Contains z) (n : ℕ) :
    (a.taylor n).1.Contains (∑ j∈Finset.range n,z^j/(j.factorial:ℂ)) ∧
    (a.taylor n).2.Contains (z^n/(n.factorial:ℂ)) := by
  induction n with
  | zero => simpa only [taylor,pow_zero,Finset.range_zero,Finset.sum_empty,Nat.factorial_zero,
      Nat.cast_one,div_one,Int.cast_zero,Int.cast_one] using And.intro (contains_ofInt 0) (contains_ofInt 1)
  | succ n ih =>
    change ((taylor a n).1.add (taylor a n).2).Contains _ ∧ (((taylor a n).2.mul a).divNat (n+1)).Contains _
    rw [Finset.sum_range_succ,show z^(n+1)/((n+1).factorial:ℂ)=z^n/(n.factorial:ℂ)*z/((n+1:ℕ):ℂ) by
      rw [pow_succ,Nat.factorial_succ,Nat.cast_mul];ring]
    exact ⟨contains_add ih.1 ih.2,contains_divNat (contains_mul ih.2 h) _⟩

private theorem squareN_contains {a : CGrid} {z : ℂ} (h : a.Contains z) (n : ℕ) :
    (a.squareN n).Contains (z^(2^n)) := by
  induction n with
  | zero => simpa only [squareN,pow_zero,pow_one] using h
  | succ n ih => simpa only [squareN,pow_succ 2 n,pow_mul,sq] using contains_mul ih ih

private theorem taylor16_widen {a : CGrid} {z : ℂ} (h : a.Contains z) (small : ‖z‖≤1/4) :
    ((a.taylor 16).1.widen 32).Contains (Complex.exp z) := by
  let S := ∑ j∈Finset.range 16,z^j/(j.factorial:ℂ)
  have err : ‖Complex.exp z-S‖≤32/(Grid.denom:ℝ) := by
    have est := Complex.exp_bound' (x:=z) (n:=16) (by norm_num; linarith)
    apply est.trans
    calc _ ≤ (1/4:ℝ)^16/(Nat.factorial 16:ℝ)*2 := by gcongr
         _ ≤ _ := by norm_num [Grid.denom,Nat.factorial]
  have er := (Complex.abs_re_le_norm (Complex.exp z-S)).trans err
  have ei := (Complex.abs_im_le_norm (Complex.exp z-S)).trans err
  rw [Complex.sub_re] at er
  rw [Complex.sub_im] at ei
  have conv (y : ℝ) (hy : |y|≤32/(Grid.denom:ℝ)) : |(Grid.denom:ℝ)*y|≤(32:ℤ) := by
    rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    have k := (le_div_iff₀ Grid.real_denom_pos).mp hy
    norm_num only [Int.cast_ofNat]
    linarith
  exact contains_widen (taylor_contains h 16).1 (conv _ er) (conv _ ei)

theorem trigPoint_contains (a : ℤ) (hl : -64*Grid.denom≤a) (hu : a≤64*Grid.denom) :
    (trigPoint a).Contains (Complex.exp (((a:ℝ)/Grid.denom:ℝ)*I)) := by
  let y := (a:ℝ)/(Grid.denom:ℝ)
  let raw : Grid := ⟨a,a,decide (-64*Grid.denom≤a ∧ a≤64*Grid.denom)⟩
  have actual : raw.Contains y := by
    intro _
    change (a:ℝ)≤(Grid.denom:ℝ)*y ∧ (Grid.denom:ℝ)*y≤(a:ℝ)
    rw [show (Grid.denom:ℝ)*y=(a:ℝ) by dsimp [y];field_simp [Grid.real_denom_pos.ne']]
    exact ⟨le_rfl,le_rfl⟩
  let z : ℂ := (y:ℂ)*I/256
  have yi : |y|≤64 := by
    apply abs_le.mpr
    constructor
    · exact (le_div_iff₀ Grid.real_denom_pos).mpr (by exact_mod_cast hl)
    · exact (div_le_iff₀ Grid.real_denom_pos).mpr (by exact_mod_cast hu)
  have small : ‖z‖≤1/4 := by
    dsimp only [z]
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_I,mul_one]
    norm_num
    linarith
  have base : ((imaginary raw).divNat 256).Contains z := by
    simpa only [z,Nat.cast_ofNat] using contains_divNat (contains_imaginary actual) 256
  have result := squareN_contains (taylor16_widen base small) 8
  change (trigPoint a).Contains ((Complex.exp z)^(2^8:ℕ)) at result
  rw [← Complex.exp_nat_mul] at result
  have eq : ((2^8:ℕ):ℂ)*z=(y:ℂ)*I := by dsimp only [z];norm_num;ring
  rw [eq] at result
  exact result

theorem trigBox_contains {a : Grid} {x : ℝ} (h : a.Contains x) :
    (trigBox a).Contains (Complex.exp ((x:ℂ)*I)) := by
  let m := (a.lo+a.hi)/2
  let r := max (m-a.lo) (a.hi-m)
  let y := (m:ℝ)/(Grid.denom:ℝ)
  have coord (f : ℝ → ℝ) (lip : ∀ x y,|f x-f y|≤|x-y|) (g : Grid) (hg : g.Contains (f y))
      (ok : a.ok=true) : (g.widen r).Contains (f x) := by
    have range := h ok
    have hl : (m:ℝ)-(a.lo:ℝ)≤(r:ℝ) := by exact_mod_cast (le_max_left (m-a.lo) (a.hi-m))
    have hu : (a.hi:ℝ)-(m:ℝ)≤(r:ℝ) := by exact_mod_cast (le_max_right (m-a.lo) (a.hi-m))
    have center : (Grid.denom:ℝ)*y=(m:ℝ) := by dsimp [y];field_simp [Grid.real_denom_pos.ne']
    apply Grid.contains_widen hg
    rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    apply (mul_le_mul_of_nonneg_left (lip x y) Grid.real_denom_pos.le).trans
    calc
      (Grid.denom:ℝ)*|x-y|=|(Grid.denom:ℝ)*(x-y)| := by rw [abs_mul,abs_of_pos Grid.real_denom_pos]
      _ ≤ (r:ℝ) := by
        rw [mul_sub,center]
        apply abs_le.mpr
        constructor <;> linarith only [range.1,range.2,hl,hu]
  have components (v : ℝ) : (Complex.exp ((v:ℂ)*I)).re=Real.cos v ∧ (Complex.exp ((v:ℂ)*I)).im=Real.sin v := by
    rw [Complex.exp_ofReal_mul_I]
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add,and_self]
  constructor
  · intro valid
    change ((trigPoint m).re.ok && (a.ok && decide (-64*Grid.denom≤m ∧ m≤64*Grid.denom)))=true at valid
    simp only [Bool.and_eq_true,decide_eq_true_eq] at valid
    have midpoint := (trigPoint_contains m valid.2.2.1 valid.2.2.2).1
    rw [(components y).1] at midpoint
    rw [(components x).1]
    exact coord Real.cos Real.abs_cos_sub_cos_le _ midpoint valid.2.1 valid.1
  · intro valid
    change ((trigPoint m).im.ok && (a.ok && decide (-64*Grid.denom≤m ∧ m≤64*Grid.denom)))=true at valid
    simp only [Bool.and_eq_true,decide_eq_true_eq] at valid
    have midpoint := (trigPoint_contains m valid.2.2.1 valid.2.2.2).2
    rw [(components y).2] at midpoint
    rw [(components x).2]
    exact coord Real.sin Real.abs_sin_sub_sin_le _ midpoint valid.2.1 valid.1

theorem contains_exp {a : CGrid} {z : ℂ} (h : a.Contains z) : a.exp.Contains (Complex.exp z) := by
  have hr := Grid.contains_squared (Grid.contains_squared (Grid.contains_exp (Grid.contains_divNat (n:=4) h.1)))
  have exponent : (Real.exp (z.re/((4:ℕ):ℝ))^2)^2=Real.exp z.re := by
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul];congr 1;norm_num;ring
  rw [exponent] at hr
  have e : Complex.exp z=((Real.exp z.re:ℝ):ℂ)*Complex.exp ((z.im:ℂ)*I) := by
    rw [Complex.ofReal_exp,← Complex.exp_add,Complex.re_add_im]
  rw [e]
  exact contains_scale hr (trigBox_contains h.2)

end TwoAxisHelicoid.PdfVertical.CGrid
#print axioms TwoAxisHelicoid.PdfVertical.CGrid.contains_exp
