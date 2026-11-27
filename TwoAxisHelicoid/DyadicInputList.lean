import TwoAxisHelicoid.DyadicExpressionTrace

namespace TwoAxisHelicoid

def dyadicInputList (xs : List DyadicBall) (i : ℕ) : DyadicBall := xs[i]?.getD .zero
noncomputable def complexInputList (xs : List ℂ) (i : ℕ) : ℂ := xs[i]?.getD 0

theorem dyadicInputList_contains {prec : ℕ} {bs : List DyadicBall} {vs : List ℂ}
    (h : List.Forall₂ (fun b v => (b.toBall prec).Contains v) bs vs) :
    ∀ i, ((dyadicInputList bs i).toBall prec).Contains (complexInputList vs i) := by
  induction h with
  | nil => intro i; exact DyadicBall.zero_contains prec
  | @cons b v bs vs hb h ih =>
    intro i
    cases i with
    | zero => exact hb
    | succ i => exact ih i

end TwoAxisHelicoid
