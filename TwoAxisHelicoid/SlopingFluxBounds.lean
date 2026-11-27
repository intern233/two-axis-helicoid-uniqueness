import TwoAxisHelicoid.TraceDataSlopingFlux
import TwoAxisHelicoid.TraceDataHorizontalBridge
import TwoAxisHelicoid.OriginalCoordinatePeriods

namespace TwoAxisHelicoid
set_option maxHeartbeats 1000000
attribute [local irreducible] thetaA
open Complex Set MeasureTheory

noncomputable def reflectedSlopingFlux (t a s : ℝ) : ℝ :=
  (((1-I*t)/2)*(thetaA t a (originalPeriodPath t s)+thetaA t a (originalPeriodPath t (-s)))).im

namespace TraceData

theorem checked_three_expression_contains (cfg : BallConfig) {a b c : DyadicBall} {x y z : ℂ}
    (ha : (a.interpret.toBall cfg.prec).Contains x) (hb : (b.interpret.toBall cfg.prec).Contains y)
    (hc : (c.interpret.toBall cfg.prec).Contains z) (e : BallExpression) (w : DyadicExpressionTrace)
    (h : w.check cfg (threeDyadic a b c) e = true) :
    (w.output.interpret.toBall cfg.prec).Contains (e.interpret.value (TwoAxisHelicoid.threeValues x y z)) := by
  have he := w.interpret_check cfg (threeDyadic a b c) e
  rw [interpret_threeDyadic] at he
  have hd := (TwoAxisHelicoid.DyadicExpressionTrace.check_eq_true ..).mp (he.trans h)
  simpa only [DyadicExpressionTrace.interpret_output,BallConfig.interpret_prec] using
    w.interpret.sound cfg.interpret _ _ (TwoAxisHelicoid.threeDyadic_contains ha hb hc) _ hd

private theorem sloping_input_contains {b : DyadicBall} {prec : ℕ} {l r : ℚ} {s : ℝ}
    (h : (b.toBall prec).coarsens (ComplexBall.realInterval l r)) (hl : (l:ℝ) ≤ s) (hr : s ≤ (r:ℝ)) :
    (b.interpret.toBall prec).Contains (s:ℂ) := by
  apply TwoAxisHelicoid.ComplexBall.coarsen_contains (TwoAxisHelicoid.ComplexBall.realInterval_contains hl hr)
  simpa only [TwoAxisHelicoid.ComplexBall.coarsens,TwoAxisHelicoid.ComplexBall.realInterval,TwoAxisHelicoid.QComplex.absUpper,
    TwoAxisHelicoid.QComplex.sub,TwoAxisHelicoid.QComplex.add,TwoAxisHelicoid.QComplex.neg,TwoAxisHelicoid.QComplex.ofRat,TwoAxisHelicoid.DyadicBall.toBall,
    ComplexBall.coarsens,ComplexBall.realInterval,QComplex.absUpper,QComplex.sub,QComplex.add,
    QComplex.neg,QComplex.ofRat,DyadicBall.toBall,DyadicBall.interpret,rat_abs_eq] using! h

private theorem sloping_im_le_of_ball {b : DyadicBall} {prec : ℕ} {z : ℂ}
    (h : (b.interpret.toBall prec).Contains z)
    (hu : (b.toBall prec).center.im+(b.toBall prec).radius ≤ -(1/32:ℚ)) : z.im ≤ -(1/32:ℝ) := by
  let B := b.interpret.toBall prec
  have hv := (Complex.abs_im_le_norm (z-B.center.val)).trans h
  have hr : z.im-(B.center.im:ℝ) ≤ (B.radius:ℝ) := (le_abs_self _).trans hv
  have hq : B.center.im+B.radius ≤ -(1/32:ℚ) := hu
  have hq' : ((B.center.im+B.radius:ℚ):ℝ) ≤ ((-(1/32:ℚ)):ℝ) := by exact_mod_cast hq
  push_cast at hq'
  linarith

private theorem value_sloping_plus (t s : ℝ) :
    (slopingFluxPointExpression true).interpret.value (TwoAxisHelicoid.threeValues ((1-I*t)/2) (s:ℂ) 0) = originalPeriodPath t s := by
  change (TwoAxisHelicoid.BallExpression.add (.neg (.rational 1)) (.mul (.input 0) (.input 1))).value _ = _
  simp only [TwoAxisHelicoid.BallExpression.value,TwoAxisHelicoid.BallExpression.value_rational,TwoAxisHelicoid.threeValues,Rat.cast_one,originalPeriodPath]
  ring

private theorem value_sloping_minus (t s : ℝ) :
    (slopingFluxPointExpression false).interpret.value (TwoAxisHelicoid.threeValues ((1-I*t)/2) (s:ℂ) 0) = originalPeriodPath t (-s) := by
  change (TwoAxisHelicoid.BallExpression.sub (.neg (.rational 1)) (.mul (.input 0) (.input 1))).value _ = _
  simp only [TwoAxisHelicoid.BallExpression.sub,TwoAxisHelicoid.BallExpression.value,TwoAxisHelicoid.BallExpression.value_rational,TwoAxisHelicoid.threeValues,Rat.cast_one,originalPeriodPath,Complex.ofReal_neg]
  ring

/-- The original dyadic cell separately encloses both reflected theta kernels. -/
theorem SlopingFluxCell.kernel_enclosures (w : SlopingFluxCell) (S : TwoAxisHelicoid.HorizontalRangeSetup) (hS : S.Valid)
    (p : RangeDyadicParameters) (v : DyadicBall) {t a s : ℝ} (ht : (S.lower:ℝ) ≤ t)
    (hq : (p.q.output.interpret.toBall S.config.prec).Contains (exp (-Real.pi*t)))
    (ha : (p.abscissa.interpret.toBall S.config.prec).Contains (a:ℂ))
    (hc : (p.coefficient.output.interpret.toBall S.config.prec).Contains (thetaACoefficient t a))
    (hv : (v.interpret.toBall S.config.prec).Contains ((1-I*t)/2)) {l r : ℚ}
    (hl : (l:ℝ) ≤ s) (hr : s ≤ (r:ℝ)) (hw : w.check (horizontalSetupOf S) p v l r = true) :
    (w.plusTheta.output.interpret.toBall S.config.prec).Contains (thetaA t a (originalPeriodPath t s)) ∧
    (w.minusTheta.output.interpret.toBall S.config.prec).Contains (thetaA t a (originalPeriodPath t (-s))) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hw
  obtain ⟨hbs,hp,hm,hpθ,hmθ,_,_⟩ := hw
  have hs := sloping_input_contains hbs hl hr
  have zero := TwoAxisHelicoid.DyadicBall.zero_contains S.config.prec
  have ep : (w.plusPoint.output.interpret.toBall S.config.prec).Contains (originalPeriodPath t s) := by
    have e := checked_three_expression_contains (horizontalSetupOf S).config (a := v) (b := w.parameter) (c := .zero) hv hs zero (slopingFluxPointExpression true) w.plusPoint hp
    rw [value_sloping_plus] at e
    exact e
  have em : (w.minusPoint.output.interpret.toBall S.config.prec).Contains (originalPeriodPath t (-s)) := by
    have e := checked_three_expression_contains (horizontalSetupOf S).config (a := v) (b := w.parameter) (c := .zero) hv hs zero (slopingFluxPointExpression false) w.minusPoint hm
    rw [value_sloping_minus] at e
    exact e
  obtain ⟨hP,_⟩ := w.plusTheta.interpret.horizontal_sound S hS ht hq ha hc ep
    (w.plusTheta.horizontal_valid_of_check_as S _ rfl _ _ _ _ hpθ)
  obtain ⟨hM,_⟩ := w.minusTheta.interpret.horizontal_sound S hS ht hq ha hc em
    (w.minusTheta.horizontal_valid_of_check_as S _ rfl _ _ _ _ hmθ)
  simpa only [DyadicThetaATrace.interpret_output,horizontalSetupOf] using And.intro hP hM

/-- The finite witness checks the genuine theta kernel on both linear
pieces, including the original sloping tangent rather than just its real
projection. -/
theorem SlopingFluxCell.sound (w : SlopingFluxCell) (S : TwoAxisHelicoid.HorizontalRangeSetup) (hS : S.Valid)
    (p : RangeDyadicParameters) (v : DyadicBall) {t a s : ℝ} (ht : (S.lower:ℝ) ≤ t)
    (hq : (p.q.output.interpret.toBall S.config.prec).Contains (exp (-Real.pi*t)))
    (ha : (p.abscissa.interpret.toBall S.config.prec).Contains (a:ℂ))
    (hc : (p.coefficient.output.interpret.toBall S.config.prec).Contains (thetaACoefficient t a))
    (hv : (v.interpret.toBall S.config.prec).Contains ((1-I*t)/2)) {l r : ℚ}
    (hl : (l:ℝ) ≤ s) (hr : s ≤ (r:ℝ)) (hw : w.check (horizontalSetupOf S) p v l r = true) :
    reflectedSlopingFlux t a s ≤ -(1/32:ℝ) := by
  obtain ⟨hP,hM⟩ := w.kernel_enclosures S hS p v ht hq ha hc hv hl hr hw
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hw
  obtain ⟨_,_,_,_,_,hY,hupper⟩ := hw
  have h := checked_three_expression_contains (horizontalSetupOf S).config (a := v) (b := w.plusTheta.output) (c := w.minusTheta.output) hv
    hP hM
    slopingFluxPairExpression w.pair hY
  exact sloping_im_le_of_ball h hupper

theorem CheckedSlopingFluxCover.sound (S : TwoAxisHelicoid.HorizontalRangeSetup) (hS : S.Valid)
    (p : RangeDyadicParameters) (v : DyadicBall) {t a : ℝ} (ht : (S.lower:ℝ) ≤ t)
    (hq : (p.q.output.interpret.toBall S.config.prec).Contains (exp (-Real.pi*t)))
    (ha : (p.abscissa.interpret.toBall S.config.prec).Contains (a:ℂ))
    (hc : (p.coefficient.output.interpret.toBall S.config.prec).Contains (thetaACoefficient t a))
    (hv : (v.interpret.toBall S.config.prec).Contains ((1-I*t)/2)) {l r : ℚ}
    (C : CheckedSlopingFluxCover (horizontalSetupOf S) p v l r) :
    ∀ s ∈ Icc (l:ℝ) r, reflectedSlopingFlux t a s ≤ -(1/32:ℝ) := by
  induction C with
  | cell w l r hw => exact fun _ hs => w.sound S hS p v ht hq ha hc hv hs.1 hs.2 hw
  | @join l m r _ _ h₁ h₂ =>
    intro s hs
    rcases le_total s (m:ℝ) with h | h
    · exact h₁ s ⟨hs.1,h⟩
    · exact h₂ s ⟨h,hs.2⟩

end TraceData
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.TraceData.CheckedSlopingFluxCover.sound
