import TwoAxisHelicoid.ThetaEnclosure

/-! Reuse three exponentials to evaluate a finite theta sum by exact recurrences. -/

namespace TwoAxisHelicoid
open ComplexBall

def imaginaryBall : ComplexBall := point ⟨0, 1⟩

theorem imaginaryBall_contains : imaginaryBall.Contains Complex.I := by
  have hI : (⟨0, 1⟩ : QComplex).val = Complex.I := by
    apply Complex.ext <;> norm_num [QComplex.val]
  rw [← hI]
  exact point_contains _

def qComplexPow (c : QComplex) : ℕ → QComplex
  | 0 => QComplex.ofRat 1
  | n+1 => (qComplexPow c n).mul c

@[simp] theorem qComplexPow_val (c : QComplex) (n : ℕ) :
    (qComplexPow c n).val = c.val^n := by
  induction n with
  | zero => simp [qComplexPow]
  | succ n ih => simp [qComplexPow, ih, pow_succ]

def fastThetaTerm (prec j k : ℕ) (bc bp bm : ComplexBall) : ComplexBall :=
  roundedMul prec
    (roundedMul prec
      (roundedMul prec (rational ((if k%4<2 then 1 else -1)*(2*k+1 : ℚ)^j)) bc)
      (point ((qComplexPow ⟨0, 1⟩ j).mul ⟨0, -1/2⟩)))
    (roundedAdd prec bp (neg (roundedMul prec (rational ((-1 : ℚ)^j)) bm)))

theorem fastThetaTerm_contains (prec j k : ℕ) {t : ℝ} {v : ℂ}
    {bc bp bm : ComplexBall}
    (hc : bc.Contains (Complex.exp (-Real.pi*t*k*(k+1)/2)))
    (hp : bp.Contains (Complex.exp ((2*k+1 : ℂ)*v*Complex.I)))
    (hm : bm.Contains (Complex.exp (-((2*k+1 : ℂ)*v)*Complex.I))) :
    (fastThetaTerm prec j k bc bp bm).Contains (thetaTerm t j k v) := by
  have hfactor : (point ((qComplexPow ⟨0, 1⟩ j).mul ⟨0, -1/2⟩)).Contains
      (Complex.I^j/(2*Complex.I)) := by
    convert point_contains ((qComplexPow ⟨0, 1⟩ j).mul ⟨0, -1/2⟩) using 1
    simp only [QComplex.val_mul, qComplexPow_val]
    have hI : (⟨0, 1⟩ : QComplex).val = Complex.I := by
      apply Complex.ext <;> norm_num [QComplex.val]
    have hhalf : (⟨0, -1/2⟩ : QComplex).val = -(Complex.I/2) := by
      apply Complex.ext <;> norm_num [QComplex.val]
    rw [hI, hhalf]
    field_simp
    simp [Complex.I_sq]
  have hb := roundedMul_contains (roundedMul_contains
    (roundedMul_contains (rational_contains ((if k%4<2 then 1 else -1)*(2*k+1 : ℚ)^j))
      hc prec) hfactor prec)
    (roundedAdd_contains hp (neg_contains
      (roundedMul_contains (rational_contains ((-1 : ℚ)^j)) hm prec)) prec) prec
  convert hb using 1
  · rfl
  · unfold thetaTerm sineJet thetaSign
    rw [Complex.ofReal_exp]
    push_cast
    split_ifs <;> ring

def fastThetaLoop (prec j : ℕ) (bq bp2 bm2 : ComplexBall) :
    ℕ → ℕ → ComplexBall → ComplexBall → ComplexBall → ComplexBall → ComplexBall
  | 0, _, _, _, _, _ => rational 0
  | N+1, k, bc, bs, bp, bm => roundedAdd prec (fastThetaTerm prec j k bc bp bm)
      (fastThetaLoop prec j bq bp2 bm2 N (k+1)
        (roundedMul prec bc bs) (roundedMul prec bs bq)
        (roundedMul prec bp bp2) (roundedMul prec bm bm2))

theorem fastThetaLoop_contains (prec j : ℕ) {t : ℝ} {v : ℂ}
    {bq bp2 bm2 : ComplexBall}
    (hq : bq.Contains (Complex.exp (-Real.pi*t)))
    (hp2 : bp2.Contains (Complex.exp (2*v*Complex.I)))
    (hm2 : bm2.Contains (Complex.exp (-2*v*Complex.I))) (N : ℕ) :
    ∀ (k : ℕ) (bc bs bp bm : ComplexBall),
    bc.Contains (Complex.exp (-Real.pi*t*k*(k+1)/2)) →
    bs.Contains (Complex.exp (-Real.pi*t*(k+1))) →
    bp.Contains (Complex.exp ((2*k+1 : ℂ)*v*Complex.I)) →
    bm.Contains (Complex.exp (-((2*k+1 : ℂ)*v)*Complex.I)) →
    (fastThetaLoop prec j bq bp2 bm2 N k bc bs bp bm).Contains
      (∑ n ∈ Finset.range N, thetaTerm t j (k+n) v) := by
  induction N with
  | zero =>
    intro k bc bs bp bm hc hs hp hm
    simpa [fastThetaLoop] using rational_contains 0
  | succ N ih =>
    intro k bc bs bp bm hc hs hp hm
    have hc' : (roundedMul prec bc bs).Contains
        (Complex.exp (-Real.pi*t*(k+1)*(k+1+1)/2)) := by
      convert roundedMul_contains hc hs prec using 1
      rw [← Complex.exp_add]
      congr 1
      ring
    have hs' : (roundedMul prec bs bq).Contains
        (Complex.exp (-Real.pi*t*(k+1+1))) := by
      convert roundedMul_contains hs hq prec using 1
      rw [← Complex.exp_add]
      congr 1
      ring
    have hp' : (roundedMul prec bp bp2).Contains
        (Complex.exp ((2*(k+1)+1 : ℂ)*v*Complex.I)) := by
      convert roundedMul_contains hp hp2 prec using 1
      rw [← Complex.exp_add]
      congr 1
      ring
    have hm' : (roundedMul prec bm bm2).Contains
        (Complex.exp (-((2*(k+1)+1 : ℂ)*v)*Complex.I)) := by
      convert roundedMul_contains hm hm2 prec using 1
      rw [← Complex.exp_add]
      congr 1
      ring
    have htail := ih (k+1) _ _ _ _ (by simpa only [Nat.cast_add, Nat.cast_one] using hc')
      (by simpa only [Nat.cast_add, Nat.cast_one] using hs')
      (by simpa only [Nat.cast_add, Nat.cast_one] using hp')
      (by simpa only [Nat.cast_add, Nat.cast_one] using hm')
    have hsum := roundedAdd_contains (fastThetaTerm_contains prec j k hc hp hm) htail prec
    convert hsum using 1
    · rfl
    · rw [Finset.sum_range_succ']
      simp only [Nat.add_zero, Nat.add_left_comm, add_comm]

end TwoAxisHelicoid
