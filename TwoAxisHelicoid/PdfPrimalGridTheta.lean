import TwoAxisHelicoid.PdfPrimalGridExpression
import TwoAxisHelicoid.PdfPrimalGridJetTails

namespace TwoAxisHelicoid.PdfVertical
open Complex

structure ThetaGridState where
  sum : CGrid
  coef : CGrid
  step : CGrid
  pos : CGrid
  neg : CGrid

def thetaGridLoop (q p m : CGrid) (j : ℕ) : ℕ → ThetaGridState
  | 0 => ⟨CGrid.ofInt 0,CGrid.ofInt 1,q,p,m⟩
  | n+1 =>
    let s := thetaGridLoop q p m j n
    let term := expressionGrid (threeCGrids s.coef s.pos s.neg) (thetaSeedTermExpression j n)
    ⟨s.sum.add term,s.coef.mul s.step,s.step.mul q,s.pos.mul (p.mul p),s.neg.mul (m.mul m)⟩

def ThetaGridState.Sound (s : ThetaGridState) (j n : ℕ) (t : ℝ) (v : ℂ) :=
  s.sum.Contains (thetaPartial t j n v) ∧ s.coef.Contains (Complex.exp (-Real.pi*t*n*(n+1)/2)) ∧
    s.step.Contains (Complex.exp (-Real.pi*t*(n+1))) ∧
    s.pos.Contains (Complex.exp ((2*n+1:ℂ)*v*I)) ∧ s.neg.Contains (Complex.exp (-((2*n+1:ℂ)*v)*I))

theorem thetaGridLoop_sound {q p m : CGrid} {t : ℝ} {v : ℂ}
    (hq : q.Contains (Complex.exp (-Real.pi*t))) (hp : p.Contains (Complex.exp (v*I)))
    (hm : m.Contains (Complex.exp (-v*I))) (j n : ℕ) : (thetaGridLoop q p m j n).Sound j n t v := by
  induction n with
  | zero =>
    have zero : (CGrid.ofInt 0).Contains (0:ℂ) := by simpa only [Int.cast_zero] using CGrid.contains_ofInt 0
    have one : (CGrid.ofInt 1).Contains (1:ℂ) := by simpa only [Int.cast_one] using CGrid.contains_ofInt 1
    simpa only [ThetaGridState.Sound,thetaGridLoop,thetaPartial,Finset.range_zero,Finset.sum_empty,
      Nat.cast_zero,mul_zero,zero_mul,zero_add,zero_div,Complex.exp_zero,mul_one,one_mul,Int.cast_zero,Int.cast_one]
      using And.intro zero (And.intro one (And.intro hq (And.intro hp hm)))
  | succ n ih =>
    obtain ⟨sum,coef,step,pos,neg⟩ := ih
    have term := expressionGrid_contains (threeCGrids_contains coef pos neg) (thetaSeedTermExpression j n)
    rw [value_thetaSeedTermExpression] at term
    simp only [ThetaGridState.Sound,thetaGridLoop]
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [thetaPartial,Finset.sum_range_succ] using CGrid.contains_add sum term
    · convert CGrid.contains_mul coef step using 1
      rw [← Complex.exp_add];push_cast;congr 1;ring
    · convert CGrid.contains_mul step hq using 1
      rw [← Complex.exp_add];push_cast;congr 1;ring
    · convert CGrid.contains_mul pos (CGrid.contains_mul hp hp) using 1
      rw [← Complex.exp_add,← Complex.exp_add];push_cast;congr 1;ring
    · convert CGrid.contains_mul neg (CGrid.contains_mul hm hm) using 1
      rw [← Complex.exp_add,← Complex.exp_add];push_cast;congr 1;ring

def thetaPrimalGrid (q v : CGrid) (j : Fin 5) : CGrid :=
  ((thetaGridLoop q v.rot.exp v.neg.rot.exp j 6).sum).widen (2^55)

theorem thetaPrimalGrid_contains {q V : CGrid} {t : ℝ} {v : ℂ}
    (hq : q.Contains (Complex.exp (-Real.pi*t))) (hv : V.Contains v) (ht : 17/20≤t)
    (strip : |v.im|≤2) (j : Fin 5) : (thetaPrimalGrid q V j).Contains (thetaJet t j v) := by
  have sum := (thetaGridLoop_sound hq (CGrid.contains_exp (CGrid.contains_rot hv))
    (CGrid.contains_exp (CGrid.contains_rot (CGrid.contains_neg hv))) j 6).1
  have norm := pdf_primal_six_term_tail ht j strip
  apply CGrid.contains_widen sum
  · have re := (Complex.abs_re_le_norm _).trans norm
    rw [Complex.sub_re] at re
    rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    norm_num only [Grid.denom,Int.cast_pow,Int.cast_ofNat]
    linarith
  · have im := (Complex.abs_im_le_norm _).trans norm
    rw [Complex.sub_im] at im
    rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    norm_num only [Grid.denom,Int.cast_pow,Int.cast_ofNat]
    linarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.thetaPrimalGrid_contains
