import TwoAxisHelicoid.PdfAdaptiveChord
import TwoAxisHelicoid.PdfChordProductSound

namespace TwoAxisHelicoid.PdfVertical
open Complex

private theorem gridWidenWithNorm {a : CGrid} {z w : ℂ} {err : Grid} {e : ℝ}
    (h : a.Contains z) (hn : ‖w-z‖≤e) (he : err.Contains e) (ok : err.ok=true) :
    (a.widen err.hi).Contains w := by
  have bound := (he ok).2
  apply CGrid.contains_widen h
  · rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm (w-z)).trans hn) Grid.real_denom_pos.le).trans bound
  · rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm (w-z)).trans hn) Grid.real_denom_pos.le).trans bound

theorem truncatedChordProduct_contains {q : Grid} {s : ℝ} {seed : CGrid} {x : ℂ}
    (hq : q.Contains s) (hz : seed.Contains ((s:ℂ)*x)) (log : Bool) (N : ℕ) :
    (truncatedChordProduct N log q seed).Contains
      (if log then x*logDeriv (jacobiFactorProduct (s:ℂ)) x else jacobiFactorProduct (s:ℂ) x) := by
  let v := (chordFinite log q seed N).1
  let p := (chordFinite log q seed N).2
  let sig := Grid.value q.mag
  let tau := Grid.value p.mag
  let M := Grid.value v.mag
  have finite := chordFinite_contains hq hz log N
  change (productWithRemainder log q seed (v,p)).Contains _
  let one := Grid.ofInt 1
  have h1 : one.Contains 1 := by simpa only [Int.cast_one] using Grid.contains_int 1
  apply CGrid.contains_guard
  intro good
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,Bool.not_eq_true'] at good
  obtain ⟨⟨⟨⟨⟨⟨qok,sok⟩,pok⟩,vok⟩,eok⟩,qsmall,tailSum,tailSmall⟩,initial⟩ := good
  have sigma : ‖(s:ℂ)‖≤sig := by simpa only [Complex.norm_real,Real.norm_eq_abs] using Grid.abs_le_mag hq qok
  have q1 : sig<1 := (div_lt_one₀ Grid.real_denom_pos).mpr (by exact_mod_cast qsmall)
  have ht : ‖(s:ℂ)^(N+1)*x‖≤tau := CGrid.norm_le_mag finite.2 pok
  have t1 : tau<1 := (div_lt_one₀ Grid.real_denom_pos).mpr (by exact_mod_cast tailSmall)
  have ds := Grid.contains_sub h1 (Grid.point_contains q.mag)
  cases log
  · have accept : ((((Grid.ofInt 2).mul (Grid.point v.mag)).mul (Grid.point p.mag)).divPos
          (one.sub (Grid.point q.mag))).ok=true := eok
    have small : tau/(1-sig)≤1 := by
      apply (div_le_one₀ (sub_pos.mpr q1)).mpr
      have le : (p.mag:ℝ)+(q.mag:ℝ)≤(Grid.denom:ℝ) := by exact_mod_cast tailSum
      change (p.mag:ℝ)/Grid.denom≤1-(q.mag:ℝ)/Grid.denom
      apply (div_le_iff₀ Grid.real_denom_pos).mpr
      rw [sub_mul,one_mul,div_mul_cancel₀ _ Grid.real_denom_pos.ne']
      linarith
    have estimate := jacobiFactorProduct_finite_error sigma q1 ht (CGrid.norm_le_mag finite.1 vok) small
    have two : (Grid.ofInt 2).Contains 2 := by simpa only [Int.cast_ofNat] using Grid.contains_int 2
    exact gridWidenWithNorm finite.1 estimate (Grid.contains_div
      (Grid.contains_mul (Grid.contains_mul two (Grid.point_contains v.mag)) (Grid.point_contains p.mag)) ds) accept
  · have seed1 : seed.mag<Grid.denom := by simpa using initial
    have small : ‖(s:ℂ)‖*‖x‖<1 := by
      rw [← norm_mul]
      exact (CGrid.norm_le_mag hz sok).trans_lt ((div_lt_one₀ Grid.real_denom_pos).mpr (by exact_mod_cast seed1))
    have estimate := jacobiEulerLog_finite_error sigma q1 small ht t1
    exact gridWidenWithNorm finite.1 estimate (Grid.contains_div (Grid.point_contains p.mag)
      (Grid.contains_mul ds (Grid.contains_sub h1 (Grid.point_contains p.mag)))) eok

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.truncatedChordProduct_contains
