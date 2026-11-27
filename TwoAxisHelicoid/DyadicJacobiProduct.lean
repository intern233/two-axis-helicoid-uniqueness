import TwoAxisHelicoid.JacobiFiniteProducts
import TwoAxisHelicoid.DyadicInflate
import TwoAxisHelicoid.DyadicThetaTerm

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000

namespace DyadicBall

def normUpper (prec : ℕ) (b : DyadicBall) : ℚ :=
  (b.toBall prec).center.absUpper+(b.toBall prec).radius

theorem norm_le_normUpper {prec : ℕ} {b : DyadicBall} {z : ℂ}
    (hb : (b.toBall prec).Contains z) : ‖z‖ ≤ (b.normUpper prec : ℝ) :=
  ComplexBall.norm_le hb

end DyadicBall

structure DyadicJacobiProductState where
  product : DyadicBall
  term : DyadicBall
  deriving Repr

inductive DyadicJacobiProductLoop where
  | zero
  | step (previous : DyadicJacobiProductLoop) (factor : DyadicBall)
      (next : DyadicJacobiProductState)
  deriving Repr

namespace DyadicJacobiProductLoop

def length : DyadicJacobiProductLoop → ℕ
  | .zero => 0
  | .step p _ _ => p.length+1

def state (prec : ℕ) (bz : DyadicBall) : DyadicJacobiProductLoop → DyadicJacobiProductState
  | .zero => ⟨.one prec, bz⟩
  | .step _ _ s => s

def Valid (prec : ℕ) (bq bz : DyadicBall) : DyadicJacobiProductLoop → Prop
  | .zero => True
  | .step p factor next =>
    let s := p.state prec bz
    p.Valid prec bq bz ∧
    DyadicBall.ChecksAdd factor (.one prec) s.term.neg ∧
    DyadicBall.ChecksMul prec next.product s.product factor ∧
    DyadicBall.ChecksMul prec next.term s.term bq

instance instDecidableValid (prec : ℕ) (bq bz : DyadicBall)
    (w : DyadicJacobiProductLoop) : Decidable (w.Valid prec bq bz) :=
  match w with
  | .zero => instDecidableTrue
  | .step p factor next => by
    haveI := instDecidableValid prec bq bz p
    unfold Valid
    infer_instance

theorem sound {bq bz : DyadicBall} {Q x : ℂ} (prec : ℕ)
    (hq : (bq.toBall prec).Contains Q) (hz : (bz.toBall prec).Contains (Q*x))
    (w : DyadicJacobiProductLoop) (hw : w.Valid prec bq bz) :
    ((w.state prec bz).product.toBall prec).Contains (jacobiFiniteProduct Q x w.length) ∧
    ((w.state prec bz).term.toBall prec).Contains (Q^(w.length+1)*x) := by
  induction w with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa [state, length, jacobiFiniteProduct] using DyadicBall.one_contains prec
    · simpa [state, length] using hz
  | step p factor next ih =>
    rcases hw with ⟨hprev, hfactor, hprod, hterm⟩
    rcases ih hprev with ⟨hp, ht⟩
    have hf := DyadicBall.add_contains (DyadicBall.one_contains prec) (DyadicBall.neg_contains ht) hfactor
    simp only [← sub_eq_add_neg] at hf
    constructor
    · have h := DyadicBall.mul_contains hp hf hprod
      simpa only [state, length, jacobiFiniteProduct, Finset.prod_range_succ] using h
    · have h := DyadicBall.mul_contains ht hq hterm
      change (next.term.toBall prec).Contains _
      convert h using 1
      simp only [length, pow_succ]
      ring

end DyadicJacobiProductLoop

structure DyadicJacobiProductTrace where
  loop : DyadicJacobiProductLoop
  output : DyadicBall
  deriving Repr

namespace DyadicJacobiProductTrace

def Valid (prec err : ℕ) (bq bz : DyadicBall) (w : DyadicJacobiProductTrace) : Prop :=
  let s := w.loop.state prec bz
  let σ := bq.normUpper prec
  let τ := s.term.normUpper prec
  let M := s.product.normUpper prec
  w.loop.Valid prec bq bz ∧ σ < 1 ∧ τ/(1-σ) ≤ 1 ∧
    2*M*τ/(1-σ) ≤ (err : ℚ)/DyadicBall.denominator prec ∧
    w.output.Coarsens (s.product.inflate err)

instance (prec err : ℕ) (bq bz : DyadicBall) (w : DyadicJacobiProductTrace) :
    Decidable (w.Valid prec err bq bz) := by unfold Valid; infer_instance

theorem sound {bq bz : DyadicBall} {Q x : ℂ} (prec err : ℕ)
    (hq : (bq.toBall prec).Contains Q) (hz : (bz.toBall prec).Contains (Q*x))
    (w : DyadicJacobiProductTrace) (hw : w.Valid prec err bq bz) :
    (w.output.toBall prec).Contains (jacobiFactorProduct Q x) := by
  rcases hw with ⟨hloop, hσ, hδ, herr, hout⟩
  have hs := w.loop.sound prec hq hz hloop
  have he := jacobiFactorProduct_finite_error
    (DyadicBall.norm_le_normUpper hq) (by exact_mod_cast hσ)
    (DyadicBall.norm_le_normUpper hs.2) (DyadicBall.norm_le_normUpper hs.1)
    (by exact_mod_cast hδ)
  have herr' : 2*((w.loop.state prec bz).product.normUpper prec : ℝ)*
      ((w.loop.state prec bz).term.normUpper prec : ℝ)/(1-(bq.normUpper prec : ℝ)) ≤
        (err : ℝ)/(DyadicBall.denominator prec : ℝ) := by exact_mod_cast herr
  exact DyadicBall.coarsen_contains (DyadicBall.inflate_contains hs.1 (he.trans herr')) hout

end DyadicJacobiProductTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicJacobiProductTrace.sound
