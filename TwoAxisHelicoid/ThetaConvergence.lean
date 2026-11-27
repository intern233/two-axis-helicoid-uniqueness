import TwoAxisHelicoid.ThetaBasic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Absolute convergence and termwise differentiation of the actual theta series. -/

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem thetaMajorant_summable {t : ℝ} (ht : 0 < t) (y : ℝ) (j : ℕ) :
    Summable (thetaMajorant t y j) := by
  have hs := (summable_pow_mul_jacobiTheta₂_term_bound (y / Real.pi)
    (T := t / 2) (by positivity) j).comp_injective
      (fun (a b : ℕ) => (Int.ofNat_inj.mp : (a : ℤ) = (b : ℤ) → a = b))
  have hsNat : Summable (fun n : ℕ => (n : ℝ)^j *
      Real.exp (-Real.pi * (t / 2 * n^2 - 2 * (y / Real.pi) * n))) := by
    simpa only [Function.comp_def, Int.cast_abs, Int.cast_natCast, Nat.abs_cast] using hs
  apply (hsNat.mul_left (Real.exp y * 3^j)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (2 * n + 1 : ℝ)^j ≤ (3 * n : ℝ)^j := by gcongr; linarith
  have heq : y + -Real.pi * (t / 2 * (n : ℝ)^2 - 2 * (y / Real.pi) * n) -
      (-Real.pi * t * n * (n + 1) / 2 + (2 * n + 1) * y) =
      Real.pi * t * n / 2 := by
    field_simp
    ring
  have he : -Real.pi * t * n * (n + 1) / 2 + (2 * n + 1) * y ≤
      y + -Real.pi * (t / 2 * (n : ℝ)^2 - 2 * (y / Real.pi) * n) := by
    have hpos : 0 ≤ Real.pi * t * (n : ℝ) / 2 := by positivity
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaMajorant_nonneg _ _ _ _)]
  calc
    thetaMajorant t y j n ≤ (3 * n : ℝ)^j *
        Real.exp (y + -Real.pi * (t / 2 * (n : ℝ)^2 - 2 * (y / Real.pi) * n)) := by
      exact mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by positivity)
    _ = _ := by rw [Real.exp_add, mul_pow]; ring

theorem thetaTerm_summable {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ) :
    Summable (fun n => thetaTerm t j n v) :=
  (thetaMajorant_summable ht |v.im| j).of_norm_bounded
    (fun n => thetaTerm_norm_le le_rfl le_rfl j n)

theorem hasDerivAt_sineJet (j : ℕ) (z : ℂ) :
    HasDerivAt (sineJet j) (sineJet (j+1) z) z := by
  have hpos := ((hasDerivAt_id z).mul_const I).cexp
  have hneg := ((hasDerivAt_id z).neg.mul_const I).cexp
  have hd := ((hpos.sub (hneg.const_mul ((-1 : ℂ)^j))).const_mul (I^j)).div_const (2*I)
  convert hd using 1
  · rfl
  · simp only [sineJet, pow_succ, id_eq, Pi.neg_apply]
    ring

theorem hasDerivAt_thetaTerm (t : ℝ) (j n : ℕ) (v : ℂ) :
    HasDerivAt (thetaTerm t j n) (thetaTerm t (j+1) n v) v := by
  have hinner := (hasDerivAt_id v).const_mul (2 * n + 1 : ℂ)
  have hd := ((hasDerivAt_sineJet j _).comp v hinner).const_mul
    (thetaSign n * (Real.exp (-Real.pi*t*n*(n+1)/2) : ℂ) * (2*n+1 : ℂ)^j)
  convert hd using 1
  · rfl
  · simp only [thetaTerm, pow_succ, id_eq]
    ring

theorem thetaTerm_differentiable (t : ℝ) (j n : ℕ) :
    Differentiable ℂ (thetaTerm t j n) :=
  fun v => (hasDerivAt_thetaTerm t j n v).differentiableAt

theorem thetaJet_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ) :
    HasDerivAt (thetaJet t j) (thetaJet t (j+1) v) v := by
  let U : Set ℂ := {w | |w.im| < |v.im| + 1}
  have hU : IsOpen U := isOpen_lt (Complex.continuous_im.abs) continuous_const
  have hv : v ∈ U := by dsimp [U]; linarith
  have hu := thetaMajorant_summable ht (|v.im| + 1) j
  have hf : ∀ n, DifferentiableOn ℂ (thetaTerm t j n) U :=
    fun n => (thetaTerm_differentiable t j n).differentiableOn
  have hb : ∀ n w, w ∈ U → ‖thetaTerm t j n w‖ ≤ thetaMajorant t (|v.im|+1) j n :=
    fun n w hw => thetaTerm_norm_le le_rfl hw.le j n
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu hf hU hb
  have hs := Complex.hasSum_deriv_of_summable_norm hu hf hU hb hv
  have heq : deriv (thetaJet t j) v = thetaJet t (j+1) v := by
    have hterms : (fun n => deriv (thetaTerm t j n) v) =
        (fun n => thetaTerm t (j+1) n v) :=
      funext (fun n => (hasDerivAt_thetaTerm t j n v).deriv)
    rw [hterms] at hs
    exact hs.tsum_eq.symm
  rw [← heq]
  exact (hd.differentiableAt (hU.mem_nhds hv)).hasDerivAt

theorem thetaJet_iteratedDeriv {t : ℝ} (ht : 0 < t) (j : ℕ) :
    iteratedDeriv j (thetaJet t 0) = thetaJet t j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun v => (thetaJet_hasDerivAt ht j v).deriv)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaMajorant_summable
#print axioms TwoAxisHelicoid.thetaJet_iteratedDeriv
