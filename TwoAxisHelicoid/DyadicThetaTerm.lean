import TwoAxisHelicoid.DyadicExpressionTrace
import TwoAxisHelicoid.ThetaBasic

namespace TwoAxisHelicoid

def threeDyadic (a b c : DyadicBall) : ℕ → DyadicBall
  | 0 => a
  | 1 => b
  | 2 => c
  | _+3 => DyadicBall.zero

noncomputable def threeValues (a b c : ℂ) : ℕ → ℂ
  | 0 => a
  | 1 => b
  | 2 => c
  | _+3 => 0

theorem threeDyadic_contains {prec : ℕ} {ba bb bc : DyadicBall} {a b c : ℂ}
    (ha : (ba.toBall prec).Contains a) (hb : (bb.toBall prec).Contains b)
    (hc : (bc.toBall prec).Contains c) :
    ∀ n, ((threeDyadic ba bb bc n).toBall prec).Contains (threeValues a b c n) := by
  intro n
  rcases n with _ | (_ | (_ | n))
  · exact ha
  · exact hb
  · exact hc
  · exact DyadicBall.zero_contains prec

def thetaSeedTermExpression (j n : ℕ) : BallExpression :=
  .mul
    (.mul (.mul (.rational ((if n%4<2 then 1 else -1)*(2*n+1 : ℚ)^j)) (.input 0))
      (.div (.pow (.const ⟨0,1⟩) j) (.const ⟨0,2⟩)))
    (.sub (.input 1) (.mul (.rational ((-1 : ℚ)^j)) (.input 2)))

theorem value_thetaSeedTermExpression (t : ℝ) (v : ℂ) (j n : ℕ) :
    (thetaSeedTermExpression j n).value
      (threeValues (Complex.exp (-Real.pi*t*n*(n+1)/2))
        (Complex.exp ((2*n+1 : ℂ)*v*Complex.I))
        (Complex.exp (-((2*n+1 : ℂ)*v)*Complex.I))) = thetaTerm t j n v := by
  have hI : (⟨0,1⟩ : QComplex).val = Complex.I := by
    apply Complex.ext <;> norm_num [QComplex.val]
  have h2I : (⟨0,2⟩ : QComplex).val = 2*Complex.I := by
    apply Complex.ext <;> norm_num [QComplex.val]
  simp only [thetaSeedTermExpression, BallExpression.value, BallExpression.value_rational,
    BallExpression.value_div, BallExpression.value_sub, BallExpression.value_pow,
    threeValues, hI, h2I]
  unfold thetaTerm sineJet thetaSign
  rw [Complex.ofReal_exp]
  push_cast
  split_ifs <;> ring

theorem dyadic_thetaTerm_contains {bt bp bm : DyadicBall} {t : ℝ} {v : ℂ}
    (cfg : BallConfig) (j n : ℕ) (w : DyadicExpressionTrace)
    (ht : (bt.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t*n*(n+1)/2)))
    (hp : (bp.toBall cfg.prec).Contains (Complex.exp ((2*n+1 : ℂ)*v*Complex.I)))
    (hm : (bm.toBall cfg.prec).Contains (Complex.exp (-((2*n+1 : ℂ)*v)*Complex.I)))
    (hw : w.Valid cfg (threeDyadic bt bp bm) (thetaSeedTermExpression j n)) :
    (w.output.toBall cfg.prec).Contains (thetaTerm t j n v) := by
  have h := w.sound cfg _ _ (threeDyadic_contains ht hp hm) _ hw
  rw [value_thetaSeedTermExpression] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.dyadic_thetaTerm_contains
