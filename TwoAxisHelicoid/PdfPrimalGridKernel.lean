import TwoAxisHelicoid.PdfPrimalGridTheta
import TwoAxisHelicoid.PdfChordProductSound
import TwoAxisHelicoid.HorizontalEnclosure
import TwoAxisHelicoid.ThetaSymmetry

namespace TwoAxisHelicoid.PdfVertical
open Complex

def checkedPrimalJet (q V : CGrid) (j : Fin 5) : CGrid :=
  (thetaPrimalGrid q V j).guard (V.im.ok && decide (V.im.mag≤2*Grid.denom))

theorem checkedPrimalJet_contains {q V : CGrid} {t : ℝ} {v : ℂ}
    (hq : q.Contains (Complex.exp (-Real.pi*t))) (hv : V.Contains v) (ht : 17/20≤t)
    (j : Fin 5) : (checkedPrimalJet q V j).Contains (thetaJet t j v) := by
  apply CGrid.contains_guard
  intro oks
  obtain ⟨ok,bound⟩ := Bool.and_eq_true_iff.mp oks
  apply thetaPrimalGrid_contains hq hv ht _ j
  apply (Grid.abs_le_mag hv.2 ok).trans
  rw [Grid.value,div_le_iff₀ Grid.real_denom_pos]
  exact_mod_cast of_decide_eq_true bound

structure PrimalThetaParameters where
  q : CGrid
  aArgument : CGrid
  exponent : Grid
  coefficient : Grid

def primalThetaParameters (t a : Grid) : PrimalThetaParameters :=
  let p := Grid.pi.divNat 2
  let qa := CGrid.real ((Grid.pi.mul t).neg.exp)
  let aa := CGrid.real (p.mul a)
  let num := (checkedPrimalJet qa (CGrid.ofInt 0) 1).re
  let den := (checkedPrimalJet qa aa 0).re
  ⟨qa,aa,Grid.pi.mul (a.sub (Grid.ofInt 1)),((p.mul num).divPos den).squared⟩

def PrimalThetaParameters.Sound (p : PrimalThetaParameters) (t a : ℝ) : Prop :=
  p.q.Contains (Complex.exp (-Real.pi*t)) ∧ p.aArgument.Contains (Real.pi*a/2) ∧
  p.exponent.Contains (Real.pi*(a-1)) ∧ (CGrid.real p.coefficient).Contains (thetaACoefficient t a)

private theorem jet_ofReal_eq (t : ℝ) (j : ℕ) (x : ℝ) :
    (((thetaJet t j (x:ℂ)).re:ℝ):ℂ)=thetaJet t j x := by
  apply Complex.ext
  · rfl
  · exact (thetaJet_real t j x).symm

theorem primalThetaParameters_sound {T A : Grid} {t a : ℝ}
    (tBox : T.Contains t) (aBox : A.Contains a) (ht : 17/20≤t) :
    (primalThetaParameters T A).Sound t a := by
  have h := Grid.contains_divNat (n:=2) Grid.contains_pi
  let q := CGrid.real ((Grid.pi.mul T).neg.exp)
  have hq : q.Contains (Complex.exp (-Real.pi*t)) := by
    simpa only [Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_mul,neg_mul]
      using CGrid.contains_real (Grid.contains_exp (Grid.contains_neg (Grid.contains_mul Grid.contains_pi tBox)))
  let aa := CGrid.real ((Grid.pi.divNat 2).mul A)
  have ha : aa.Contains (((Real.pi/2*a:ℝ):ℂ)) := CGrid.contains_real (Grid.contains_mul h aBox)
  have z : (CGrid.ofInt 0).Contains ((0:ℝ):ℂ) := by simpa only [Int.cast_zero,Complex.ofReal_zero] using CGrid.contains_ofInt 0
  have num := (checkedPrimalJet_contains hq z ht 1).1
  have den := (checkedPrimalJet_contains hq ha ht 0).1
  have K := Grid.contains_squared (Grid.contains_div (Grid.contains_mul h num) den)
  have hK := CGrid.contains_real K
  have eq : (((Real.pi/2*(thetaJet t 1 ((0:ℝ):ℂ)).re/(thetaJet t 0 (((Real.pi/2*a:ℝ):ℂ))).re)^2:ℝ):ℂ)=thetaACoefficient t a := by
    rw [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_mul,
      jet_ofReal_eq t 1 0, jet_ofReal_eq t 0 (Real.pi/2*a)]
    unfold thetaACoefficient
    push_cast
    rw [show (Real.pi:ℂ)/2*(a:ℂ)=Real.pi*a/2 by ring]
    ring
  refine ⟨hq,?_,Grid.contains_mul Grid.contains_pi (Grid.contains_sub aBox (by simpa using Grid.contains_int 1)),?_⟩
  · have align : (Real.pi:ℂ)*(a:ℂ)/2=((Real.pi/2*a:ℝ):ℂ) := by push_cast; ring
    exact align.symm ▸ ha
  · rwa [← eq]

def primalThetaValue (p : PrimalThetaParameters) (v : CGrid) : CGrid :=
  let den := checkedPrimalJet p.q v 0
  let num := checkedPrimalJet p.q (v.sub p.aArgument) 0
  let first := checkedPrimalJet p.q v 1
  let ratio := num.div den
  CGrid.real p.coefficient |>.mul ((ratio.mul ratio).mul ((first.div den).scale p.exponent).exp)

theorem primalThetaValue_contains {p : PrimalThetaParameters} {t a : ℝ}
    (data : p.Sound t a) (ht : 17/20≤t) {v : CGrid} {z : ℂ}
    (hv : v.Contains (Real.pi*z/2)) : (primalThetaValue p v).Contains (thetaA t a z) := by
  obtain ⟨q,aa,coef,parameter⟩ := data
  have shifted := CGrid.contains_sub hv aa
  rw [show (Real.pi:ℂ)*z/2-Real.pi*a/2=Real.pi*(z-a)/2 by ring] at shifted
  have den := checkedPrimalJet_contains q hv ht 0
  have num := checkedPrimalJet_contains q shifted ht 0
  have first := checkedPrimalJet_contains q hv ht 1
  have ratio := CGrid.contains_div num den
  have quot := CGrid.contains_div first den
  have exp := CGrid.contains_exp (CGrid.contains_scale coef quot)
  have result := CGrid.contains_mul parameter (CGrid.contains_mul (CGrid.contains_mul ratio ratio) exp)
  simpa only [primalThetaValue,Fin.val_zero,Fin.val_one,thetaA,thetaACoefficient,thetaQuotient,pow_two,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_one,mul_comm (Real.pi:ℂ) ((a:ℂ)-1),mul_assoc] using result

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.primalThetaParameters_sound
#print axioms TwoAxisHelicoid.PdfVertical.primalThetaValue_contains
