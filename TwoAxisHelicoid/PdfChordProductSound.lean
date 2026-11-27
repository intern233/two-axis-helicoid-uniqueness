import TwoAxisHelicoid.PdfChordInterval
import TwoAxisHelicoid.PdfComplexGridSound
import TwoAxisHelicoid.JacobiFiniteEuler

namespace TwoAxisHelicoid.PdfVertical
open Complex

noncomputable def Grid.value (n : ℤ) : ℝ := (n:ℝ)/(Grid.denom:ℝ)

theorem Grid.denom_mul_value (n : ℤ) : (Grid.denom:ℝ)*Grid.value n=(n:ℝ) := by
  unfold value
  field_simp [Grid.real_denom_pos.ne']

theorem Grid.point_contains (n : ℤ) : (Grid.point n).Contains (Grid.value n) := by
  intro _
  rw [denom_mul_value]
  exact ⟨le_rfl,le_rfl⟩

theorem Grid.abs_le_mag {a : Grid} {x : ℝ} (h : a.Contains x) (ok : a.ok=true) : |x|≤Grid.value a.mag := by
  have l : -(a.lo:ℝ)≤(a.mag:ℝ) := by exact_mod_cast (le_max_left (-a.lo) a.hi)
  have r : (a.hi:ℝ)≤(a.mag:ℝ) := by exact_mod_cast (le_max_right (-a.lo) a.hi)
  apply (le_div_iff₀ Grid.real_denom_pos).mpr
  calc |x| * (Grid.denom:ℝ) = |(Grid.denom:ℝ)*x| := by rw [abs_mul,abs_of_pos Grid.real_denom_pos,mul_comm]
       _ ≤ (a.mag:ℝ) := abs_le.mpr ⟨by linarith [(h ok).1],(h ok).2.trans r⟩

theorem CGrid.norm_le_mag {a : CGrid} {z : ℂ} (h : a.Contains z) (ok : a.ok=true) :
    ‖z‖≤Grid.value a.mag := by
  obtain ⟨r,i⟩ := Bool.and_eq_true_iff.mp ok
  apply (Complex.norm_le_abs_re_add_abs_im z).trans
  simpa only [Grid.value,CGrid.mag,Int.cast_add,add_div] using
    add_le_add (Grid.abs_le_mag h.1 r) (Grid.abs_le_mag h.2 i)

theorem CGrid.contains_guard {a : CGrid} {z : ℂ} {flag : Bool} (h : flag=true → a.Contains z) :
    (a.guard flag).Contains z := by
  constructor
  · intro ok
    obtain ⟨o,f⟩ := Bool.and_eq_true_iff.mp ok
    exact (h f).1 o
  · intro ok
    obtain ⟨o,f⟩ := Bool.and_eq_true_iff.mp ok
    exact (h f).2 o

private theorem CGrid.widen_error {a : CGrid} {z w : ℂ} {err : Grid} {e : ℝ}
    (h : a.Contains z) (hn : ‖w-z‖≤e) (he : err.Contains e) (ok : err.ok=true) :
    (a.widen err.hi).Contains w := by
  have bound := (he ok).2
  apply CGrid.contains_widen h
  · rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm (w-z)).trans hn) Grid.real_denom_pos.le).trans bound
  · rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm (w-z)).trans hn) Grid.real_denom_pos.le).trans bound

theorem chordFinite_contains {q : Grid} {s : ℝ} {seed : CGrid} {x : ℂ}
    (hq : q.Contains s) (hz : seed.Contains ((s:ℂ)*x)) (log : Bool) (N : ℕ) :
    (chordFinite log q seed N).1.Contains (if log then jacobiFiniteEuler s x N else jacobiFiniteProduct s x N) ∧
      (chordFinite log q seed N).2.Contains ((s:ℂ)^(N+1)*x) := by
  induction N with
  | zero =>
    constructor
    · cases log
      · simpa only [chordFinite,jacobiFiniteProduct,Finset.range_zero,Finset.prod_empty,
          Bool.false_eq_true,ite_false,Int.cast_one] using CGrid.contains_ofInt 1
      · simpa only [chordFinite,jacobiFiniteEuler,Finset.range_zero,Finset.sum_empty,ite_true,
          Int.cast_zero] using CGrid.contains_ofInt 0
    · simpa only [chordFinite,Nat.zero_add,pow_one] using hz
  | succ n ih =>
    obtain ⟨v,p⟩ := ih
    have one : (CGrid.ofInt 1).Contains 1 := by simpa only [Int.cast_one] using CGrid.contains_ofInt 1
    have term := CGrid.contains_sub one p
    constructor
    · cases log
      · change ((chordFinite false q seed n).1.mul _).Contains (jacobiFiniteProduct s x (n+1))
        rw [jacobiFiniteProduct,Finset.prod_range_succ]
        exact CGrid.contains_mul v term
      · change ((chordFinite true q seed n).1.add _).Contains (jacobiFiniteEuler s x (n+1))
        rw [jacobiFiniteEuler,Finset.sum_range_succ]
        simpa only [ite_true,jacobiFiniteEuler,neg_mul] using CGrid.contains_add v (CGrid.contains_div (CGrid.contains_neg p) term)
    · change ((chordFinite log q seed n).2.scale q).Contains _
      have e : (s:ℂ)*((s:ℂ)^(n+1)*x)=(s:ℂ)^(n+1+1)*x := by ring
      rw [← e]
      exact CGrid.contains_scale hq p

/-- Each accepted tail is bounded against the infinite Jacobi product
or its logarithmic derivative. The assumptions concern exactly Q and Q*x. -/
theorem chordEulerProduct_contains {q : Grid} {s : ℝ} {seed : CGrid} {x : ℂ}
    (hq : q.Contains s) (hz : seed.Contains ((s:ℂ)*x)) (log : Bool) :
    (chordEulerProduct log q seed).Contains
      (if log then x*logDeriv (jacobiFactorProduct (s:ℂ)) x else jacobiFactorProduct (s:ℂ) x) := by
  let v := (chordFinite log q seed 10).1
  let p := (chordFinite log q seed 10).2
  let sig := Grid.value q.mag
  let tau := Grid.value p.mag
  let M := Grid.value v.mag
  have finite := chordFinite_contains hq hz log 10
  let one := Grid.ofInt 1
  have h1 : one.Contains 1 := by simpa only [Int.cast_one] using Grid.contains_int 1
  apply CGrid.contains_guard
  intro good
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,Bool.not_eq_true'] at good
  obtain ⟨⟨⟨⟨⟨⟨qok,sok⟩,pok⟩,vok⟩,eok⟩,qsmall,tailSum,tailSmall⟩,initial⟩ := good
  have sigma : ‖(s:ℂ)‖≤sig := by simpa only [Complex.norm_real,Real.norm_eq_abs] using Grid.abs_le_mag hq qok
  have q1 : sig<1 := (div_lt_one₀ Grid.real_denom_pos).mpr (by exact_mod_cast qsmall)
  have ht : ‖(s:ℂ)^(10+1)*x‖≤tau := CGrid.norm_le_mag finite.2 pok
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
    exact CGrid.widen_error finite.1 estimate (Grid.contains_div
      (Grid.contains_mul (Grid.contains_mul two (Grid.point_contains v.mag)) (Grid.point_contains p.mag)) ds) accept
  · have seed1 : seed.mag<Grid.denom := by simpa using initial
    have small : ‖(s:ℂ)‖*‖x‖<1 := by
      rw [← norm_mul]
      exact (CGrid.norm_le_mag hz sok).trans_lt ((div_lt_one₀ Grid.real_denom_pos).mpr (by exact_mod_cast seed1))
    have estimate := jacobiEulerLog_finite_error sigma q1 small ht t1
    exact CGrid.widen_error finite.1 estimate (Grid.contains_div (Grid.point_contains p.mag)
      (Grid.contains_mul ds (Grid.contains_sub h1 (Grid.point_contains p.mag)))) eok

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.chordEulerProduct_contains

