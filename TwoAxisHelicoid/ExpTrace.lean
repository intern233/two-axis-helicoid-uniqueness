import TwoAxisHelicoid.ThetaDisk

/-! Explicit intermediate disks turn exponential evaluation into a sequence of
small kernel checks. The trace is untrusted input; every transition is proved. -/

namespace TwoAxisHelicoid
open ComplexBall

inductive ExpTaylorTrace where
  | zero
  | step (previous : ExpTaylorTrace) (sum term : ComplexBall)
  deriving Repr

namespace ExpTaylorTrace

def length : ExpTaylorTrace → ℕ
  | .zero => 0
  | .step p _ _ => p.length+1

def sum : ExpTaylorTrace → ComplexBall
  | .zero => rational 0
  | .step _ s _ => s

def term : ExpTaylorTrace → ComplexBall
  | .zero => rational 1
  | .step _ _ t => t

def Valid (prec : ℕ) (b : ComplexBall) : ExpTaylorTrace → Prop
  | .zero => True
  | .step p s t => p.Valid prec b ∧
      s.coarsens (roundedAdd prec p.sum p.term) ∧
      t.coarsens (roundedMul prec (roundedMul prec p.term b) (rational (1/(p.length+1 : ℚ))))

instance instDecidableValid (prec : ℕ) (b : ComplexBall) (w : ExpTaylorTrace) :
    Decidable (w.Valid prec b) :=
  match w with
  | .zero => instDecidableTrue
  | .step p s t => by
    haveI := instDecidableValid prec b p
    unfold Valid
    infer_instance

theorem sound {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (prec : ℕ)
    (w : ExpTaylorTrace) (hw : w.Valid prec b) :
    w.sum.Contains (∑ k ∈ Finset.range w.length, z^k/(k.factorial : ℂ)) ∧
    w.term.Contains (z^w.length/(w.length.factorial : ℂ)) := by
  induction w with
  | zero =>
    constructor
    · simpa [sum, length] using rational_contains 0
    · simpa [term, length] using rational_contains 1
  | step p s t ih =>
    have hp := ih hw.1
    constructor
    · apply coarsen_contains ?_ hw.2.1
      simpa only [length, Finset.sum_range_succ] using roundedAdd_contains hp.1 hp.2 prec
    · have h := coarsen_contains (roundedMul_contains (roundedMul_contains hp.2 hb prec)
        (rational_contains (1/(p.length+1 : ℚ))) prec) hw.2.2
      change t.Contains _
      convert h using 1
      dsimp only [length]
      push_cast
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp

end ExpTaylorTrace

inductive SquareTrace where
  | zero
  | step (previous : SquareTrace) (out : ComplexBall)
  deriving Repr

namespace SquareTrace

def length : SquareTrace → ℕ
  | .zero => 0
  | .step p _ => p.length+1

def output (base : ComplexBall) : SquareTrace → ComplexBall
  | .zero => base
  | .step _ b => b

def Valid (prec : ℕ) (base : ComplexBall) : SquareTrace → Prop
  | .zero => True
  | .step p b => p.Valid prec base ∧ b.coarsens (roundedMul prec (p.output base) (p.output base))

instance instDecidableValid (prec : ℕ) (b : ComplexBall) (w : SquareTrace) :
    Decidable (w.Valid prec b) :=
  match w with
  | .zero => instDecidableTrue
  | .step p out => by
    haveI := instDecidableValid prec b p
    unfold Valid
    infer_instance

theorem sound {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (prec : ℕ)
    (w : SquareTrace) (hw : w.Valid prec b) : (w.output b).Contains (z^(2^w.length)) := by
  induction w with
  | zero => simpa [output, length] using hb
  | step p out ih =>
    have hp := ih hw.1
    have h := coarsen_contains (roundedMul_contains hp hp prec) hw.2
    simpa only [output, length, pow_succ, ← pow_add, ← two_mul, Nat.mul_comm 2 (2^p.length)] using h

end SquareTrace

structure ExpTrace where
  taylor : ExpTaylorTrace
  enclosure : ComplexBall
  squares : SquareTrace
  deriving Repr

namespace ExpTrace

def output (w : ExpTrace) : ComplexBall := w.squares.output w.enclosure

def Valid (cfg : BallConfig) (b : ComplexBall) (w : ExpTrace) : Prop :=
  let scaled := scale (1/(2^cfg.squarings : ℚ)) b
  w.taylor.length = cfg.terms ∧ w.taylor.Valid cfg.prec scaled ∧ expGuard scaled cfg.terms ∧
    w.enclosure.coarsens (round cfg.prec (w.taylor.sum.inflate (expError scaled cfg.terms))) ∧
    w.squares.length = cfg.squarings ∧ w.squares.Valid cfg.prec w.enclosure

instance (cfg : BallConfig) (b : ComplexBall) (w : ExpTrace) : Decidable (w.Valid cfg b) := by
  unfold Valid
  infer_instance

theorem sound {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (cfg : BallConfig)
    (w : ExpTrace) (hw : w.Valid cfg b) : w.output.Contains (Complex.exp z) := by
  rcases hw with ⟨hlen, htaylor, hguard, hencl, hslen, hsquares⟩
  let scaled := scale (1/(2^cfg.squarings : ℚ)) b
  let u := z/(2^cfg.squarings : ℂ)
  have hu : scaled.Contains u := by
    convert scale_contains hb (1/(2^cfg.squarings : ℚ)) using 1
    push_cast
    ring
  have hp := (w.taylor.sound hu cfg.prec htaylor).1
  rw [hlen] at hp
  have hn := norm_le hu
  have hg : ‖u‖/(cfg.terms+1 : ℝ) ≤ 1/2 := by
    have hc : ((scaled.center.absUpper+scaled.radius : ℚ) : ℝ)/(cfg.terms+1 : ℝ) ≤ 1/2 := by
      change expGuard scaled cfg.terms at hguard
      unfold expGuard at hguard
      have hc : (((scaled.center.absUpper+scaled.radius)/(cfg.terms+1 : ℚ) : ℚ) : ℝ) ≤
          ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hguard
      simpa using hc
    exact (div_le_div_of_nonneg_right hn (by positivity)).trans hc
  have herr := Complex.exp_bound' (x := u) (n := cfg.terms)
    (by simpa only [Nat.cast_succ] using hg)
  have herr' : ‖Complex.exp u-∑ k ∈ Finset.range cfg.terms, u^k/(k.factorial : ℂ)‖ ≤
      (expError scaled cfg.terms : ℝ) := by
    apply herr.trans
    unfold expError
    push_cast
    gcongr
    simpa only [Rat.cast_add] using hn
  have he := coarsen_contains (round_contains (inflate_contains hp herr') cfg.prec) hencl
  have hs := w.squares.sound he cfg.prec hsquares
  rw [hslen] at hs
  have heq : (Complex.exp u)^(2^cfg.squarings) = Complex.exp z := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [u]
    push_cast
    field_simp
  simpa only [output, heq] using hs

end ExpTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ExpTrace.sound
