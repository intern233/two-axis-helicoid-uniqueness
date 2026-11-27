import TwoAxisHelicoid.PdfUniformParameterCell
import TwoAxisHelicoid.PdfPrimalGridKernel
import TwoAxisHelicoid.PeriodicThetaSampling
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

/-- Input of the theta function on the strip about its real half period. -/
def primalStripArgument (T X Y : Grid) : CGrid :=
  (⟨X,Y.add (T.divNat 2)⟩ : CGrid).scale (Grid.pi.divNat 2)

theorem primalStripArgument_contains {T X Y : Grid} {t : ℝ} {z : ℂ}
    (ht : T.Contains t) (hx : X.Contains z.re) (hy : Y.Contains z.im) :
    (primalStripArgument T X Y).Contains (Real.pi*(z+I*((t/2:ℝ):ℂ))/2) := by
  have arg : (⟨X,Y.add (T.divNat 2)⟩ : CGrid).Contains (z+I*((t/2:ℝ):ℂ)) := by
    simp only [CGrid.Contains,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,
      mul_zero,sub_zero,add_zero,zero_add]
    exact ⟨hx,Grid.contains_add hy (Grid.contains_divNat ht)⟩
  have h := CGrid.contains_scale (Grid.contains_divNat (n:=2) Grid.contains_pi) arg
  have aligned : ((Real.pi/(2:ℕ):ℝ):ℂ)*(z+I*((t/2:ℝ):ℂ))=Real.pi*(z+I*((t/2:ℝ):ℂ))/2 := by
    push_cast
    ring
  rw [← aligned]
  exact h

theorem right_sample_error_small :
    let r := Real.exp (-(2*Real.pi*((8:ℝ)*(3/8))))
    2*((4096:ℝ)*r/(1-r))≤1/1000 := by
  let r := Real.exp (-(2*Real.pi*((8:ℝ)*(3/8))))
  have exp18 : (27/10:ℝ)^18≤Real.exp 18 := by
    rw [show (18:ℝ)=(18:ℕ)*(1:ℝ) by norm_num,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have upper : r≤1/(27/10:ℝ)^18 := by
    dsimp only [r]
    simp only [Real.exp_neg,one_div]
    exact inv_anti₀ (by positivity) (exp18.trans (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])))
  change 2*((4096:ℝ)*r/(1-r))≤_
  have small : r≤1/10000000 := upper.trans (by norm_num)
  have den : 0<1-r := by linarith
  rw [← mul_div_assoc,div_le_iff₀ den]
  linarith

def primalStripOutput (T : Grid) (p : PrimalThetaParameters) (xlo xhi ylo yhi : ℚ) : CGrid :=
  primalThetaValue p (primalStripArgument T (Grid.ofRats xlo xhi) (Grid.ofRats ylo yhi))

theorem primalStripOutput_contains {T : Grid} {p : PrimalThetaParameters} {t a : ℝ}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t) {z : ℂ} {xl xu yl yu : ℚ}
    (x : z.re∈Icc (xl:ℝ) (xu:ℝ)) (y : z.im∈Icc (yl:ℝ) (yu:ℝ)) :
    (primalStripOutput T p xl xu yl yu).Contains (thetaA t a (z+I*((t/2:ℝ):ℂ))) :=
  primalThetaValue_contains ps ht (primalStripArgument_contains ts
    (Grid.contains_rats x.1 x.2) (Grid.contains_rats y.1 y.2))

/-- A Cartesian grid certificate for a two bisection-free horizontal edges suffices
for the eight-point rule on all ten right-end rectangles. -/
theorem right_strip_bound_of_eight {t a : ℝ} {T : Grid} {p : PrimalThetaParameters}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t)
    (checked : ∀ i : Fin 8, ∀ flag : Bool,
      let y : ℚ := if flag then 3/8 else -3/8
      let b := primalStripOutput T p (-1+(i:ℚ)/8) (-1+((i:ℚ)+1)/8) y y
      b.ok=true ∧ b.mag≤4096*Grid.denom) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/8 → ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤4096 := by
  intro z x y
  obtain ⟨i,ilo,ihi⟩ := closed_uniform_cell (N:=8) (by decide) (by norm_num : (-1:ℝ)<0) x
  norm_num only [sub_neg_eq_add,zero_add,one_mul,Nat.cast_ofNat] at ilo ihi
  obtain ⟨flag,he⟩ : ∃ flag : Bool, z.im=(((if flag then 3/8 else -3/8 : ℚ)):ℝ) := by
    by_cases pos : 0≤z.im
    · refine ⟨true,?_⟩
      rw [abs_of_nonneg pos] at y
      simpa only [ite_true,Rat.cast_div,Rat.cast_ofNat] using y
    · refine ⟨false,?_⟩
      rw [abs_of_neg (lt_of_not_ge pos)] at y
      norm_num
      linarith
  obtain ⟨ok,mag⟩ := checked i flag
  have val := primalStripOutput_contains ts ps ht (z:=z)
    (xl:=-1+(i:ℚ)/8) (xu:=-1+((i:ℚ)+1)/8)
    (yl:=if flag then 3/8 else -3/8) (yu:=if flag then 3/8 else -3/8)
    (by push_cast;exact ⟨ilo,ihi⟩) ⟨he.ge,he.le⟩
  apply (CGrid.norm_le_mag val ok).trans
  rw [Grid.value,div_le_iff₀ Grid.real_denom_pos]
  exact_mod_cast mag

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_strip_bound_of_eight
