import TwoAxisHelicoid.HelicoidGroundState
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace TwoAxisHelicoid
open Set MeasureTheory Filter Metric Function
open scoped ContDiff
set_option maxHeartbeats 1200000

/-- Every continuous nonnegative one-dimensional potential which is positive
at the origin has a smooth compactly supported negative direction. The proof
uses dilated bump functions and an exact scaling of their Dirichlet energy. -/
theorem exists_smooth_compact_negative_direction {V : ℝ → ℝ}
    (hV : Continuous V) (hn : ∀ x, 0 ≤ V x) (hp : 0 < V 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∫ x : ℝ, (deriv ψ x)^2-V x*ψ x^2) < 0 := by
  let χ : ContDiffBump (0 : ℝ) := default
  have hχ : ContDiff ℝ ∞ χ := χ.contDiff
  have hχs : HasCompactSupport (fun x => χ x^2) :=
    χ.hasCompactSupport.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  have hBcont : Continuous (fun x => V x*χ x^2) := hV.mul (χ.continuous.pow 2)
  have hBint : Integrable (fun x => V x*χ x^2) :=
    hBcont.integrable_of_hasCompactSupport hχs.mul_left
  let B := ∫ x : ℝ, V x*χ x^2
  have hB : 0 < B := by
    apply integral_pos_of_integrable_nonneg_nonzero hBcont hBint
      (fun x => mul_nonneg (hn x) (sq_nonneg _)) (x := 0)
    rw [show χ 0 = 1 from χ.eventuallyEq_one.self_of_nhds]
    simpa using hp.ne'
  let K := ∫ x : ℝ, (deriv χ x)^2
  obtain ⟨R,hlarge⟩ := exists_gt (max (2 : ℝ) (K/B))
  have hR2 : 2 < R := (le_max_left _ _).trans_lt hlarge
  have hR : 0 < R := by linarith
  have hKR : K/R < B := by
    apply (div_lt_iff₀ hR).mpr
    have h := (div_lt_iff₀ hB).mp ((le_max_right _ _).trans_lt hlarge)
    nlinarith
  let ψ : ℝ → ℝ := fun x => χ (x/R)
  have hψ : ContDiff ℝ ∞ ψ := hχ.comp (contDiff_id.div_const R)
  have hψs : HasCompactSupport ψ := by
    simpa only [smul_eq_mul,mul_comm,← div_eq_mul_inv] using
      χ.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')
  have hψd (x : ℝ) : deriv ψ x = deriv χ (x/R)/R := by
    have hd := ((hχ.differentiable (by simp)) (x/R)).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const R)
    simpa only [ψ,Function.comp_def,id_eq,one_div,one_mul,div_eq_mul_inv] using hd.deriv
  have hψDint : Integrable (fun x => (deriv ψ x)^2) := by
    have hc : Continuous (fun x => (deriv ψ x)^2) := (hψ.continuous_deriv (by simp)).pow 2
    exact hc.integrable_of_hasCompactSupport
      (hψs.deriv.comp_left (g := fun x : ℝ => x^2) (by norm_num))
  have hψPint : Integrable (fun x => V x*ψ x^2) :=
    (hV.mul (hψ.continuous.pow 2)).integrable_of_hasCompactSupport
      (show HasCompactSupport (fun x => V x*ψ x^2) from
        (hψs.comp_left (g := fun x : ℝ => x^2) (by norm_num)).mul_left)
  have henergy : (∫ x : ℝ, (deriv ψ x)^2) = K/R := by
    simp_rw [hψd,div_pow]
    rw [integral_div,Measure.integral_comp_div (fun x : ℝ => (deriv χ x)^2) R]
    simp only [abs_of_pos hR,smul_eq_mul]
    dsimp [K]
    field_simp
  have hcompare (x : ℝ) : V x*χ x^2 ≤ V x*ψ x^2 := by
    by_cases hx : χ x = 0
    · simp only [hx,zero_pow (by decide : 2 ≠ 0),mul_zero]
      exact mul_nonneg (hn x) (sq_nonneg _)
    · have hxb : x ∈ ball (0 : ℝ) 2 := by
        have hmem : x ∈ support χ := hx
        simpa only [χ.support_eq,show χ.rOut = 2 from rfl] using hmem
      have hxa : |x| < 2 := by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hxb
      have hψone : ψ x = 1 := by
        apply χ.one_of_mem_closedBall
        change dist (x/R) 0 ≤ 1
        rw [dist_zero_right,Real.norm_eq_abs,abs_div,abs_of_pos hR]
        exact (div_le_one hR).mpr (by linarith)
      rw [hψone,one_pow,mul_one]
      have hχsq : χ x^2 ≤ 1 := by nlinarith [χ.nonneg' x,show χ x ≤ 1 from χ.le_one]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hχsq (hn x)
  have hpotential : B ≤ ∫ x : ℝ, V x*ψ x^2 := integral_mono hBint hψPint hcompare
  refine ⟨ψ,hψ,hψs,?_⟩
  rw [integral_sub hψDint hψPint,henergy]
  linarith

theorem exists_helicoid_smooth_compact_negative_direction :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∫ x : ℝ, (deriv ψ x)^2-2*helicoidGroundState x^2*ψ x^2) < 0 := by
  apply exists_smooth_compact_negative_direction
  · unfold helicoidGroundState
    fun_prop (disch := intros; positivity)
  · intro x; positivity
  · norm_num [helicoidGroundState]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_smooth_compact_negative_direction
#print axioms TwoAxisHelicoid.exists_helicoid_smooth_compact_negative_direction
