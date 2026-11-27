import TwoAxisHelicoid.SchrodingerTensorEnergy
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace TwoAxisHelicoid
open Set MeasureTheory Filter Function
open scoped ContDiff

noncomputable def planarQuadraticEnergy (W v : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-W p*v p^2

noncomputable def planarMass (v : ℝ × ℝ → ℝ) : ℝ := ∫ p : ℝ × ℝ, v p^2

theorem planar_slice_deriv_x {v : ℝ × ℝ → ℝ} (hv : Differentiable ℝ v) (p : ℝ × ℝ) :
    deriv (fun x => v (x,p.2)) p.1 = fderiv ℝ v p (1,0) := by
  have h := (hv p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  simpa only [Function.comp_def,id_eq] using h.deriv

theorem planar_slice_deriv_y {v : ℝ × ℝ → ℝ} (hv : Differentiable ℝ v) (p : ℝ × ℝ) :
    deriv (fun y => v (p.1,y)) p.2 = fderiv ℝ v p (0,1) := by
  have h := (hv p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  simpa only [Function.comp_def,id_eq] using h.deriv

theorem planarQuadraticEnergy_eq_schrodinger {v : ℝ × ℝ → ℝ}
    (hv : Differentiable ℝ v) (V : ℝ → ℝ) :
    planarQuadraticEnergy (fun p => V p.2) v = planarSchrodingerEnergy V v := by
  unfold planarQuadraticEnergy planarSchrodingerEnergy
  simp_rw [planar_slice_deriv_x hv,planar_slice_deriv_y hv]

theorem smooth_compact_planar_square_integrable {v : ℝ × ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hs : HasCompactSupport v) : Integrable (fun p => v p^2) := by
  have hc : Continuous (fun p => v p^2) := hv.continuous.pow 2
  exact hc.integrable_of_hasCompactSupport
    (hs.comp_left (g := fun y : ℝ => y^2) (by norm_num))

theorem smooth_compact_planar_derivative_square_integrable {v : ℝ × ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hs : HasCompactSupport v) (w : ℝ × ℝ) :
    Integrable (fun p => (fderiv ℝ v p w)^2) := by
  have hc : Continuous (fun p => fderiv ℝ v p w) :=
    (hv.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hc2 : Continuous (fun p => (fderiv ℝ v p w)^2) := hc.pow 2
  exact hc2.integrable_of_hasCompactSupport
    ((hs.fderiv_apply (𝕜 := ℝ) w).comp_left (g := fun y : ℝ => y^2) (by norm_num))

theorem smooth_compact_planar_potential_integrable {W v : ℝ × ℝ → ℝ}
    (hW : Continuous W) (hv : ContDiff ℝ ∞ v) (hs : HasCompactSupport v) :
    Integrable (fun p => W p*v p^2) :=
  (hW.mul (hv.continuous.pow 2)).integrable_of_hasCompactSupport
    (show HasCompactSupport (fun p => W p*v p^2) from
      (hs.comp_left (g := fun y : ℝ => y^2) (by norm_num)).mul_left)

theorem smooth_compact_planar_energy_integrable {W v : ℝ × ℝ → ℝ}
    (hW : Continuous W) (hv : ContDiff ℝ ∞ v) (hs : HasCompactSupport v) :
    Integrable (fun p => (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-W p*v p^2) :=
  ((smooth_compact_planar_derivative_square_integrable hv hs (1,0)).add
    (smooth_compact_planar_derivative_square_integrable hv hs (0,1))).sub
    (smooth_compact_planar_potential_integrable hW hv hs)

/-- The exact quantitative continuity of the quadratic form in its
potential on the compact support of a fixed smooth test function. -/
theorem planarQuadraticEnergy_stability {W V v : ℝ × ℝ → ℝ}
    (hW : Continuous W) (hV : Continuous V) (hv : ContDiff ℝ ∞ v)
    (hs : HasCompactSupport v) {ε : ℝ}
    (hclose : ∀ p ∈ tsupport v, |W p-V p| ≤ ε) :
    |planarQuadraticEnergy W v-planarQuadraticEnergy V v| ≤ ε*planarMass v := by
  have he : planarQuadraticEnergy W v-planarQuadraticEnergy V v =
      ∫ p : ℝ × ℝ, (V p-W p)*v p^2 := by
    rw [planarQuadraticEnergy,planarQuadraticEnergy,← integral_sub
      (smooth_compact_planar_energy_integrable hW hv hs)
      (smooth_compact_planar_energy_integrable hV hv hs)]
    congr 1
    funext p
    ring
  rw [he]
  have hbound : ∀ p, ‖(V p-W p)*v p^2‖ ≤ ε*v p^2 := by
    intro p
    by_cases hp : p ∈ tsupport v
    · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (v p)),abs_sub_comm]
      exact mul_le_mul_of_nonneg_right (hclose p hp) (sq_nonneg _)
    · have hz : v p = 0 := notMem_support.mp (fun h => hp (subset_closure h))
      simp [hz]
  have hb := norm_integral_le_of_norm_le
    ((smooth_compact_planar_square_integrable hv hs).const_mul ε) (Eventually.of_forall hbound)
  simpa only [Real.norm_eq_abs,integral_const_mul,planarMass] using hb

theorem planarQuadraticEnergy_negative_of_close {W V v : ℝ × ℝ → ℝ}
    (hW : Continuous W) (hV : Continuous V) (hv : ContDiff ℝ ∞ v)
    (hs : HasCompactSupport v) {ε : ℝ}
    (hclose : ∀ p ∈ tsupport v, |W p-V p| ≤ ε)
    (hmargin : ε*planarMass v < -planarQuadraticEnergy V v) :
    planarQuadraticEnergy W v < 0 := by
  have h := (abs_le.mp (planarQuadraticEnergy_stability hW hV hv hs hclose)).2
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.planarQuadraticEnergy_stability
#print axioms TwoAxisHelicoid.planarQuadraticEnergy_negative_of_close
