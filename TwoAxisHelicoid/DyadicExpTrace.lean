import TwoAxisHelicoid.DyadicExpError

namespace TwoAxisHelicoid
open ComplexBall

namespace DyadicBall

def zero : DyadicBall := ⟨0, 0, 0⟩
def one (prec : ℕ) : DyadicBall := ⟨denominator prec, 0, 0⟩

theorem zero_contains (prec : ℕ) : (zero.toBall prec).Contains (0 : ℂ) := by
  simp [zero, toBall, Contains, QComplex.val]
  rfl

theorem one_contains (prec : ℕ) : ((one prec).toBall prec).Contains (1 : ℂ) := by
  have hd : (0 : ℚ) < denominator prec := by exact_mod_cast denominator_pos prec
  simp [one, toBall, Contains, QComplex.val, hd.ne']
  apply Complex.ext <;> norm_num

end DyadicBall

inductive DyadicTaylorTrace where
  | zero
  | step (previous : DyadicTaylorTrace) (sum product term : DyadicBall)
  deriving Repr

namespace DyadicTaylorTrace

def length : DyadicTaylorTrace → ℕ
  | .zero => 0
  | .step p _ _ _ => p.length+1
def sum : DyadicTaylorTrace → DyadicBall
  | .zero => DyadicBall.zero
  | .step _ s _ _ => s
def term (prec : ℕ) : DyadicTaylorTrace → DyadicBall
  | .zero => DyadicBall.one prec
  | .step _ _ _ t => t
def Valid (prec : ℕ) (b : DyadicBall) : DyadicTaylorTrace → Prop
  | .zero => True
  | .step p s m t => p.Valid prec b ∧
      DyadicBall.ChecksAdd s p.sum (p.term prec) ∧
      DyadicBall.ChecksMul prec m (p.term prec) b ∧
      DyadicBall.ChecksDivNat t m (p.length+1)

instance instDecidableValid (prec : ℕ) (b : DyadicBall) (w : DyadicTaylorTrace) :
    Decidable (w.Valid prec b) :=
  match w with
  | .zero => instDecidableTrue
  | .step p s m t => by
    haveI := instDecidableValid prec b p
    unfold Valid
    infer_instance

theorem sound {prec : ℕ} {b : DyadicBall} {z : ℂ} (hb : (b.toBall prec).Contains z)
    (w : DyadicTaylorTrace) (hw : w.Valid prec b) :
    (w.sum.toBall prec).Contains (∑ k ∈ Finset.range w.length, z^k/(k.factorial : ℂ)) ∧
    ((w.term prec).toBall prec).Contains (z^w.length/(w.length.factorial : ℂ)) := by
  induction w with
  | zero =>
    constructor
    · simpa [sum, length] using DyadicBall.zero_contains prec
    · simpa [term, length] using DyadicBall.one_contains prec
  | step p s m t ih =>
    have hp := ih hw.1
    constructor
    · simpa only [sum, length, Finset.sum_range_succ] using
        DyadicBall.add_contains hp.1 hp.2 hw.2.1
    · have h := DyadicBall.divNat_contains (DyadicBall.mul_contains hp.2 hb hw.2.2.1) hw.2.2.2
      change (t.toBall prec).Contains _
      convert h using 1
      dsimp only [length]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp

end DyadicTaylorTrace

inductive DyadicSquareTrace where
  | zero
  | step (previous : DyadicSquareTrace) (out : DyadicBall)
  deriving Repr

namespace DyadicSquareTrace

def length : DyadicSquareTrace → ℕ
  | .zero => 0
  | .step p _ => p.length+1
def output (base : DyadicBall) : DyadicSquareTrace → DyadicBall
  | .zero => base
  | .step _ b => b
def Valid (prec : ℕ) (base : DyadicBall) : DyadicSquareTrace → Prop
  | .zero => True
  | .step p b => p.Valid prec base ∧ DyadicBall.ChecksMul prec b (p.output base) (p.output base)

instance instDecidableValid (prec : ℕ) (b : DyadicBall) (w : DyadicSquareTrace) :
    Decidable (w.Valid prec b) :=
  match w with
  | .zero => instDecidableTrue
  | .step p out => by
    haveI := instDecidableValid prec b p
    unfold Valid
    infer_instance

theorem sound {prec : ℕ} {b : DyadicBall} {z : ℂ} (hb : (b.toBall prec).Contains z)
    (w : DyadicSquareTrace) (hw : w.Valid prec b) :
    ((w.output b).toBall prec).Contains (z^(2^w.length)) := by
  induction w with
  | zero => simpa [output, length] using hb
  | step p out ih =>
    have hp := ih hw.1
    have h := DyadicBall.mul_contains hp hp hw.2
    simpa only [output, length, pow_succ, ← pow_add, ← two_mul, Nat.mul_comm 2 (2^p.length)] using h

end DyadicSquareTrace

structure DyadicExpTrace where
  scaled : DyadicBall
  taylor : DyadicTaylorTrace
  enclosure : DyadicBall
  squares : DyadicSquareTrace
  deriving Repr

namespace DyadicExpTrace

def output (w : DyadicExpTrace) : DyadicBall := w.squares.output w.enclosure

def Valid (cfg : BallConfig) (b : DyadicBall) (w : DyadicExpTrace) : Prop :=
  DyadicBall.ChecksDivNat w.scaled b (2^cfg.squarings) ∧
  w.taylor.length = cfg.terms ∧ w.taylor.Valid cfg.prec w.scaled ∧
  DyadicBall.ChecksExpGuard cfg.prec cfg.terms w.scaled ∧
  DyadicBall.ChecksExpError cfg.prec cfg.terms w.enclosure w.taylor.sum w.scaled ∧
  w.squares.length = cfg.squarings ∧ w.squares.Valid cfg.prec w.enclosure

instance (cfg : BallConfig) (b : DyadicBall) (w : DyadicExpTrace) : Decidable (w.Valid cfg b) := by
  unfold Valid
  infer_instance

theorem sound {b : DyadicBall} {z : ℂ} (cfg : BallConfig) (hb : (b.toBall cfg.prec).Contains z)
    (w : DyadicExpTrace) (hw : w.Valid cfg b) :
    (w.output.toBall cfg.prec).Contains (Complex.exp z) := by
  rcases hw with ⟨hscaled, hlen, htaylor, hguard, hencl, hslen, hsquares⟩
  let u := z/(2^cfg.squarings : ℂ)
  have hu : (w.scaled.toBall cfg.prec).Contains u := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using DyadicBall.divNat_contains hb hscaled
  have hp := (w.taylor.sound hu htaylor).1
  rw [hlen] at hp
  have hn := norm_le hu
  have hg := DyadicBall.checksExpGuard_sound hguard
  have hguard' : ‖u‖/(cfg.terms+1 : ℝ) ≤ 1/2 := by
    have hc : (((w.scaled.toBall cfg.prec).center.absUpper+(w.scaled.toBall cfg.prec).radius : ℚ) : ℝ)/
        (cfg.terms+1 : ℝ) ≤ 1/2 := by
      unfold expGuard at hg
      have hc : ((((w.scaled.toBall cfg.prec).center.absUpper+(w.scaled.toBall cfg.prec).radius)/
          (cfg.terms+1 : ℚ) : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hg
      simpa using hc
    exact (div_le_div_of_nonneg_right hn (by positivity)).trans hc
  have herr := Complex.exp_bound' (x := u) (n := cfg.terms)
    (by simpa only [Nat.cast_succ] using hguard')
  have herr' : ‖Complex.exp u-∑ k ∈ Finset.range cfg.terms, u^k/(k.factorial : ℂ)‖ ≤
      (expError (w.scaled.toBall cfg.prec) cfg.terms : ℝ) := by
    apply herr.trans
    unfold expError
    push_cast
    gcongr
    simpa only [Rat.cast_add] using hn
  have he := coarsen_contains (inflate_contains hp herr') (DyadicBall.checksExpError_coarsens hencl)
  have hs := w.squares.sound he hsquares
  rw [hslen] at hs
  have heq : (Complex.exp u)^(2^cfg.squarings) = Complex.exp z := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [u]
    push_cast
    field_simp
  simpa only [output, heq] using hs

end DyadicExpTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicExpTrace.sound
