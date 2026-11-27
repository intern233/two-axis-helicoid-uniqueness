import TwoAxisHelicoid.VerticalEnclosure
import TwoAxisHelicoid.DyadicInputList

namespace TwoAxisHelicoid
open ComplexBall
attribute [local irreducible] thetaJet thetaQuotient

noncomputable def rightSlopeTheta (t : ℝ) : ℂ :=
  (Real.pi^3/48:ℂ)*(3*(thetaQuotient t 2 (Real.pi/2))^2+
    2*thetaQuotient t 4 (Real.pi/2)-
    2*(thetaJet t 3 0/thetaJet t 1 0)*thetaQuotient t 2 (Real.pi/2))

def rightSlopeExpression : BallExpression :=
  let q2 := BallExpression.div (.input 1) (.input 0)
  let q4 := BallExpression.div (.input 2) (.input 0)
  let q3 := BallExpression.div (.input 4) (.input 3)
  .mul (.div (.pow .pi 3) (.rational 48))
    (.sub (.add (.mul (.rational 3) (.pow q2 2)) (.mul (.rational 2) q4))
      (.mul (.mul (.rational 2) q3) q2))

def ballInputList (xs : List ComplexBall) (i : ℕ) : ComplexBall := xs[i]?.getD (rational 0)

theorem ballInputList_contains {bs : List ComplexBall} {vs : List ℂ}
    (h : List.Forall₂ (fun b v => b.Contains v) bs vs) :
    ∀ i, (ballInputList bs i).Contains (complexInputList vs i) := by
  induction h with
  | nil => intro i; simpa [ballInputList,complexInputList] using rational_contains 0
  | @cons b v bs vs hb h ih =>
    intro i
    cases i with
    | zero => exact hb
    | succ i => exact ih i

theorem value_rightSlopeExpression (t : ℝ) :
    rightSlopeExpression.value (complexInputList [thetaJet t 0 (Real.pi/2),thetaJet t 2 (Real.pi/2),
      thetaJet t 4 (Real.pi/2),thetaJet t 1 0,thetaJet t 3 0]) = rightSlopeTheta t := by
  simp [rightSlopeExpression,BallExpression.value,complexInputList,rightSlopeTheta,thetaQuotient]

def evalRightSlope (cfg : BallConfig) (N : ℕ) (bt : ComplexBall) : Option ComplexBall := do
  let bv := verticalArgumentBall cfg (rational 1)
  let s0 ← evalTheta cfg 0 N bt bv
  let s2 ← evalTheta cfg 2 N bt bv
  let s4 ← evalTheta cfg 4 N bt bv
  let d1 ← evalTheta cfg 1 N bt (rational 0)
  let d3 ← evalTheta cfg 3 N bt (rational 0)
  BallExpression.eval cfg (ballInputList [s0,s2,s4,d1,d3]) rightSlopeExpression

theorem evalRightSlope_sound {bt : ComplexBall} {t : ℝ} (ht : bt.Contains (t:ℂ))
    (cfg : BallConfig) (N : ℕ) : Sound (evalRightSlope cfg N bt) (rightSlopeTheta t) := by
  have hv : (verticalArgumentBall cfg (rational 1)).Contains (Real.pi/2:ℂ) := by
    simpa using verticalArgumentBall_contains (a := (1:ℝ)) (by simpa using rational_contains 1) cfg
  have hz : (rational 0).Contains (0:ℂ) := by simpa using rational_contains 0
  unfold evalRightSlope
  apply bind_sound (evalTheta_sound ht hv cfg 0 N)
  intro s0 h0
  apply bind_sound (evalTheta_sound ht hv cfg 2 N)
  intro s2 h2
  apply bind_sound (evalTheta_sound ht hv cfg 4 N)
  intro s4 h4
  apply bind_sound (evalTheta_sound ht hz cfg 1 N)
  intro d1 h1
  apply bind_sound (evalTheta_sound ht hz cfg 3 N)
  intro d3 h3
  have henv := ballInputList_contains (List.Forall₂.cons h0 (.cons h2 (.cons h4 (.cons h1 (.cons h3 .nil)))))
  simpa only [value_rightSlopeExpression] using BallExpression.eval_sound cfg _ _ henv rightSlopeExpression

def certifiesRightSlope (cfg : BallConfig) (N : ℕ) (tlo thi lo hi : ℚ) : Prop :=
  match evalRightSlope cfg N (realInterval tlo thi) with
  | none => False
  | some b => lo ≤ b.center.re-b.radius ∧ b.center.re+b.radius ≤ hi

instance (cfg : BallConfig) (N : ℕ) (tlo thi lo hi : ℚ) :
    Decidable (certifiesRightSlope cfg N tlo thi lo hi) := by
  unfold certifiesRightSlope
  split <;> infer_instance

theorem certified_rightSlope_bounds (cfg : BallConfig) (N : ℕ) (tlo thi lo hi : ℚ)
    (hc : certifiesRightSlope cfg N tlo thi lo hi) {t : ℝ} (htl : (tlo:ℝ) ≤ t) (htu : t ≤ (thi:ℝ)) :
    (lo:ℝ) ≤ (rightSlopeTheta t).re ∧ (rightSlopeTheta t).re ≤ (hi:ℝ) := by
  have hs := evalRightSlope_sound (realInterval_contains htl htu) cfg N
  unfold certifiesRightSlope at hc
  cases he : evalRightSlope cfg N (realInterval tlo thi) with
  | none => simp only [he] at hc
  | some b =>
    simp only [he] at hc
    have hb := re_bounds (hs b he)
    exact ⟨(Rat.cast_le.mpr hc.1).trans hb.1,hb.2.trans (Rat.cast_le.mpr hc.2)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certified_rightSlope_bounds
