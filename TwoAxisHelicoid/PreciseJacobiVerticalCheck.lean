import TwoAxisHelicoid.DyadicJacobiSecond
import TwoAxisHelicoid.DyadicInputList
import TwoAxisHelicoid.JacobiVerticalIdentity

namespace TwoAxisHelicoid
open Complex

/-- Π is supplied as a separately proved dyadic disk. The standard
π disk suffices for sign boxes, while the root attachment stores
endpoint vertical intervals much narrower than that disk. -/
def fineRootNome (t : ℚ) : BallExpression :=
  .neg (.exp (.div (.neg (.input 0)) (.rational t)))
def fineRootAbscissa (t a : ℚ) : BallExpression :=
  .exp (.div (.neg (.mul (.input 0) (.rational a))) (.rational t))
def fineRootReciprocal : BallExpression := .div (.input 0) (.input 1)
def fineRootValue (t : ℚ) : BallExpression :=
  .mul (.pow (.div (.input 0) (.rational t)) 2) (.add (.input 1) (.input 2))

structure PreciseVerticalTrace where
  nome : DyadicExpressionTrace
  firstArg : DyadicExpressionTrace
  secondArg : DyadicExpressionTrace
  first : DyadicJacobiSecondTrace
  second : DyadicJacobiSecondTrace
  full : DyadicExpressionTrace

def PreciseVerticalTrace.Valid (w : PreciseVerticalTrace) (cfg : BallConfig) (err : ℕ)
    (bp : DyadicBall) (t a lo hi : ℚ) : Prop :=
  w.nome.Valid cfg (dyadicInputList [bp]) (fineRootNome t) ∧
  w.firstArg.Valid cfg (dyadicInputList [bp]) (fineRootAbscissa t a) ∧
  w.secondArg.Valid cfg (dyadicInputList [w.nome.output,w.firstArg.output]) fineRootReciprocal ∧
  w.first.Valid cfg err w.nome.output w.firstArg.output ∧
  w.second.Valid cfg err w.nome.output w.secondArg.output ∧
  w.full.Valid cfg (dyadicInputList [bp,w.first.output,w.second.output]) (fineRootValue t) ∧
  lo≤(w.full.output.toBall cfg.prec).center.re-(w.full.output.toBall cfg.prec).radius ∧
  (w.full.output.toBall cfg.prec).center.re+(w.full.output.toBall cfg.prec).radius≤hi

instance PreciseVerticalTrace.validDecidable (w : PreciseVerticalTrace) (cfg : BallConfig) (err : ℕ) (bp : DyadicBall) (t a lo hi : ℚ) :
    Decidable (w.Valid cfg err bp t a lo hi) := by unfold PreciseVerticalTrace.Valid; infer_instance

theorem PreciseVerticalTrace.bounds {w : PreciseVerticalTrace} {cfg : BallConfig} {err : ℕ}
    {bp : DyadicBall} (piIn : (bp.toBall cfg.prec).Contains (Real.pi:ℂ)) {t a lo hi : ℚ}
    (tpos : 0<t) (apos : 0<a) (aone : a<1) (valid : w.Valid cfg err bp t a lo hi) :
    (lo:ℝ)≤(thetaG (t:ℝ) (a:ℝ)).re ∧ (thetaG (t:ℝ) (a:ℝ)).re≤(hi:ℝ) := by
  obtain ⟨qn,ar,br,first,second,last,low,high⟩ := valid
  let Q := -Real.exp (-Real.pi/(t:ℝ))
  let r := Real.exp (-Real.pi*(a:ℝ)/(t:ℝ))
  have hpi := dyadicInputList_contains (.cons piIn .nil)
  have qs : (w.nome.output.toBall cfg.prec).Contains (Q:ℂ) := by
    simpa [fineRootNome,BallExpression.value,complexInputList,Q] using w.nome.sound cfg _ _ hpi _ qn
  have rs : (w.firstArg.output.toBall cfg.prec).Contains (r:ℂ) := by
    simpa [fineRootAbscissa,BallExpression.value,complexInputList,r] using w.firstArg.sound cfg _ _ hpi _ ar
  have bs : (w.secondArg.output.toBall cfg.prec).Contains ((Q/r:ℝ):ℂ) := by
    simpa [fineRootReciprocal,BallExpression.value,complexInputList] using
      w.secondArg.sound cfg _ _ (dyadicInputList_contains (.cons qs (.cons rs .nil))) _ br
  have hq : |Q|<1 := by
    have h := DyadicBall.norm_le_normUpper qs
    simp only [Complex.norm_real,Real.norm_eq_abs] at h
    exact h.trans_lt (by exact_mod_cast first.2.1)
  have hr : |r|<1 := by
    have h := DyadicBall.norm_le_normUpper rs
    simp only [Complex.norm_real,Real.norm_eq_abs] at h
    exact h.trans_lt (by exact_mod_cast first.2.2.1)
  have one := w.first.sound cfg err qs rs first
  have two := w.second.sound cfg err qs bs second
  have realValue : (thetaG (t:ℝ) (a:ℝ)).re=
      (Real.pi/(t:ℝ))^2*(jacobiGeometricSeries Q r+jacobiGeometricSeries Q (Q/r)) := by
    rw [thetaG_re_eq_jacobiRealE (by exact_mod_cast tpos) (by exact_mod_cast apos) (by exact_mod_cast aone)]
    rw [div_pow,jacobiRealE_two_series hq hr]
  have out := w.full.sound cfg _ _ (dyadicInputList_contains (.cons piIn (.cons one (.cons two .nil)))) _ last
  have eqn : (fineRootValue t).value (complexInputList [(Real.pi:ℂ),(jacobiGeometricSeries Q r:ℂ),
      (jacobiGeometricSeries Q (Q/r):ℂ)])=(((thetaG (t:ℝ) (a:ℝ)).re:ℝ):ℂ) := by
    rw [realValue]
    simp [fineRootValue,BallExpression.value,complexInputList]
  rw [eqn] at out
  have h := ComplexBall.re_bounds out
  simp only [Complex.ofReal_re] at h
  exact ⟨(Rat.cast_le.mpr low).trans h.1,h.2.trans (Rat.cast_le.mpr high)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.PreciseVerticalTrace.bounds
