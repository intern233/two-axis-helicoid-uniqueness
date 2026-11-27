import TwoAxisHelicoid.AnalyticTaylorBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace TwoAxisHelicoid
open MeasureTheory

structure QuadratureRule (K : ℕ) where
  node : Fin K → ℚ
  weight : Fin K → ℚ

def monomialAverage (n : ℕ) : ℚ := (1-(-1)^ (n+1))/(2*(n+1))

def QuadratureRule.ExactTo {K : ℕ} (q : QuadratureRule K) (N : ℕ) : Prop :=
  ∀ j : Fin N, ∑ i, q.weight i*(q.node i)^j.val = monomialAverage j.val

instance {K : ℕ} (q : QuadratureRule K) (N : ℕ) : Decidable (q.ExactTo N) :=
  inferInstanceAs (Decidable (∀ j : Fin N, ∑ i, q.weight i*(q.node i)^j.val = monomialAverage j.val))

def QuadratureRule.NodesInUnit {K : ℕ} (q : QuadratureRule K) : Prop :=
  ∀ i, -1 ≤ q.node i ∧ q.node i ≤ 1

instance {K : ℕ} (q : QuadratureRule K) : Decidable q.NodesInUnit :=
  inferInstanceAs (Decidable (∀ i, -1 ≤ q.node i ∧ q.node i ≤ 1))

def QuadratureRule.weightNorm {K : ℕ} (q : QuadratureRule K) : ℚ := ∑ i, |q.weight i|

noncomputable def QuadratureRule.apply {K : ℕ} (q : QuadratureRule K)
    (f : ℂ → ℂ) (c : ℂ) (h : ℝ) : ℂ :=
  ∑ i, (q.weight i : ℂ)*f (c+(h : ℂ)*(q.node i : ℂ))

noncomputable def normalizedIntegral (f : ℂ → ℂ) (c : ℂ) (h : ℝ) : ℂ :=
  (1/2 : ℂ)*(∫ x : ℝ in (-1)..1, f (c+(h : ℂ)*(x : ℂ)))

theorem normalized_integral_pow (n : ℕ) :
    (1/2 : ℂ)*(∫ x : ℝ in (-1)..1, (x : ℂ)^n) = (monomialAverage n : ℂ) := by
  simp_rw [← Complex.ofReal_pow]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  simp only [monomialAverage]
  push_cast
  field_simp
  ring

theorem normalizedIntegral_taylor (f : ℂ → ℂ) (c : ℂ) (h : ℝ) (N : ℕ) :
    normalizedIntegral (analyticTaylor f c N) c h =
      ∑ j ∈ Finset.range N,
        (j.factorial : ℂ)⁻¹*iteratedDeriv j f c*(h : ℂ)^j*(monomialAverage j : ℂ) := by
  unfold normalizedIntegral analyticTaylor analyticTaylorTerm
  simp only [add_sub_cancel_left, mul_pow]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp_rw [← mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    have hp := normalized_integral_pow j
    calc
      _ = ((j.factorial : ℂ)⁻¹*iteratedDeriv j f c*(h : ℂ)^j)*
          ((1/2 : ℂ)*(∫ x : ℝ in (-1)..1, (x : ℂ)^j)) := by ring
      _ = _ := by rw [hp]
  · intro j hj
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (j.factorial : ℂ)⁻¹*iteratedDeriv j f c*((h : ℂ)^j*(x : ℂ)^j))).intervalIntegrable _ _

theorem QuadratureRule.exact_taylor {K N : ℕ} {q : QuadratureRule K}
    (hq : q.ExactTo N) (f : ℂ → ℂ) (c : ℂ) (h : ℝ) :
    q.apply (analyticTaylor f c N) c h = normalizedIntegral (analyticTaylor f c N) c h := by
  rw [normalizedIntegral_taylor]
  unfold QuadratureRule.apply analyticTaylor analyticTaylorTerm
  simp only [add_sub_cancel_left, mul_pow]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hm : ∑ i, (q.weight i : ℂ)*(q.node i : ℂ)^j = (monomialAverage j : ℂ) := by
    exact_mod_cast hq ⟨j, Finset.mem_range.mp hj⟩
  calc
    _ = ((j.factorial : ℂ)⁻¹*iteratedDeriv j f c*(h : ℂ)^j)*
        (∑ i, (q.weight i : ℂ)*(q.node i : ℂ)^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hm]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.QuadratureRule.exact_taylor
