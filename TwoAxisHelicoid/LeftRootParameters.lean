import TwoAxisHelicoid.SmallVerticalBounds
import TwoAxisHelicoid.JacobiRootBalance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 800000
attribute [local irreducible] thetaG verticalA jacobiRealE

noncomputable def leftRootR (t : ℝ) : ℝ := Real.exp (-Real.pi*verticalA t/t)
noncomputable def leftBeta (t : ℝ) : ℝ := (leftNome t)^2/leftRootR t
noncomputable def leftEpsilon (t : ℝ) : ℝ := Real.log (leftNome t/leftRootR t)
noncomputable def leftKappa0 (t : ℝ) : ℝ := Real.pi/(2*t)
noncomputable def leftKappa (t : ℝ) : ℝ := -Real.log (leftBeta t)

theorem leftRootR_pos (t : ℝ) : 0 < leftRootR t := Real.exp_pos _
theorem leftBeta_pos (t : ℝ) : 0 < leftBeta t :=
  div_pos (sq_pos_of_pos (leftNome_pos t)) (leftRootR_pos t)

theorem jacobiRealE_at_verticalA_zero {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    jacobiRealE (-(leftNome t)^2) (leftRootR t) = 0 := by
  have ha := verticalA_spec ht
  have h := congrArg Complex.re ha.2
  rw [thetaG_re_eq_jacobiRealE ht.1 ha.1.1 ha.1.2, ← leftNome_sq ht.1] at h
  simp only [Complex.zero_re] at h
  exact (mul_eq_zero.mp h).resolve_left
    (ne_of_gt (div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos ht.1)))

theorem jacobi_root_log_ratio_bound {q r : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100)
    (hrl : q/2 < r) (hru : r < q) (hroot : jacobiRealE (-q^2) r = 0) :
    0 < Real.log (q/r) ∧ Real.log (q/r) ≤ 6*q := by
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrl.le
  have hlog : 0 < Real.log (q/r) := Real.log_pos ((one_lt_div hr).mpr hru)
  have hratio : 0 < q/r := div_pos hq0 hr
  have hs : 2*q*Real.sinh (Real.log (q/r)) = q^2/r-r := by
    rw [Real.sinh_eq, Real.exp_neg, Real.exp_log hratio]
    field_simp
  have hm := mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr hlog.le)
    (by positivity : 0 ≤ 2*q)
  rw [hs] at hm
  have hb := (jacobi_root_beta_sub_r_le hq0 hq hrl.le hru.le hroot).2
  refine ⟨hlog, ?_⟩
  nlinarith

theorem leftRootR_bounds {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    leftNome t/2 < leftRootR t ∧ leftRootR t < leftNome t :=
  exp_verticalA_small_bounds ht htu

theorem leftBeta_bounds {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    leftNome t ≤ leftBeta t ∧ leftBeta t ≤ 2*leftNome t := by
  have hr := leftRootR_bounds ht htu
  exact (jacobi_root_basic_bounds (leftNome_pos t) hr.1.le hr.2.le).2

theorem leftBeta_sub_r_bounds {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    0 ≤ leftBeta t-leftRootR t ∧ leftBeta t-leftRootR t ≤ 12*(leftNome t)^2 := by
  have hr := leftRootR_bounds ht htu
  exact jacobi_root_beta_sub_r_le (leftNome_pos t) (leftNome_lt_one_hundredth ht htu).le
    hr.1.le hr.2.le (jacobiRealE_at_verticalA_zero (small_height_mem_vertical_domain ht htu))

theorem leftEpsilon_bounds {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    0 < leftEpsilon t ∧ leftEpsilon t ≤ 6*leftNome t := by
  have hr := leftRootR_bounds ht htu
  exact jacobi_root_log_ratio_bound (leftNome_pos t) (leftNome_lt_one_hundredth ht htu).le
    hr.1 hr.2 (jacobiRealE_at_verticalA_zero (small_height_mem_vertical_domain ht htu))

theorem leftBeta_eq_nome_mul_exp (t : ℝ) : leftBeta t = leftNome t*Real.exp (leftEpsilon t) := by
  unfold leftBeta leftEpsilon
  rw [Real.exp_log (div_pos (leftNome_pos t) (leftRootR_pos t))]
  ring

theorem leftKappa_eq_kappa0_sub_epsilon (t : ℝ) : leftKappa t = leftKappa0 t-leftEpsilon t := by
  rw [leftKappa, leftBeta_eq_nome_mul_exp,
    Real.log_mul (leftNome_pos t).ne' (Real.exp_ne_zero _), Real.log_exp]
  unfold leftKappa0 leftNome
  rw [Real.log_exp]
  ring

theorem leftKappa_bounds {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    leftKappa0 t-6*leftNome t ≤ leftKappa t ∧
      leftKappa t ≤ leftKappa0 t ∧ leftKappa0 t < leftKappa t+1 := by
  have he := leftEpsilon_bounds ht htu
  have hq := leftNome_lt_one_hundredth ht htu
  rw [leftKappa_eq_kappa0_sub_epsilon]
  constructor
  · linarith
  · constructor <;> linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftBeta_sub_r_bounds
#print axioms TwoAxisHelicoid.leftKappa_bounds
