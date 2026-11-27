import TwoAxisHelicoid.HeightEndGrowth
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

/-- If the spatial image remains bounded, both real and imaginary parts of
the height coordinate remain bounded. The uniform base-line bound is
obtained from actual compact images of horizontal segments. -/
theorem height_end_bounded_image_parameter_bound {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α b R₀ Y : ℝ) (hY : 0 ≤ Y) (hRY : R₀ < Y)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F z)) 1)) z)
    (hheight : ∀ z : ℂ, R₀ < ‖z‖ → X z 2 = z.re+b)
    (hF : ∀ z : ℂ, Y ≤ ‖z‖ → |(F z).im| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ D > (0 : ℝ), ∀ z : ℂ, R₀ < ‖z‖ → ‖X z‖ ≤ B → ‖z‖ ≤ D := by
  let M := B+|b|
  have hM : 0 ≤ M := add_nonneg hB (abs_nonneg b)
  have hnp (x : ℝ) : R₀ < ‖(x : ℂ)+I*Y‖ :=
    hRY.trans_le (by simpa [abs_of_nonneg hY] using vertical_line_norm_ge_abs x Y)
  have hnm (x : ℝ) : R₀ < ‖(x : ℂ)+I*(-Y)‖ :=
    hRY.trans_le (by simpa [abs_neg,abs_of_nonneg hY] using vertical_line_norm_ge_abs x (-Y))
  have hcp : Continuous (fun x : ℝ => X ((x : ℂ)+I*Y)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hX _ (hnp x)).continuousAt.comp (f := fun x : ℝ => (x : ℂ)+I*Y)
      (show ContinuousAt (fun x : ℝ => (x : ℂ)+I*Y) x by fun_prop)
  have hcm : Continuous (fun x : ℝ => X ((x : ℂ)+I*(-Y))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hX _ (hnm x)).continuousAt.comp (f := fun x : ℝ => (x : ℂ)+I*(-Y))
      (show ContinuousAt (fun x : ℝ => (x : ℂ)+I*(-Y)) x by fun_prop)
  obtain ⟨Cp,hCp,hpBound⟩ := ((isCompact_Icc (a := -M) (b := M)).image hcp).isBounded.exists_pos_norm_le
  obtain ⟨Cm,hCm,hmBound⟩ := ((isCompact_Icc (a := -M) (b := M)).image hcm).isBounded.exists_pos_norm_le
  refine ⟨M+Y+4*(B+(Cp+Cm))+1,by positivity,?_⟩
  intro z hz hnorm
  have hv (j : Fin 3) : |X z j| ≤ B := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (X z) j).trans hnorm
  have hx : |z.re| ≤ M := by
    calc |z.re| = |X z 2-b| := by rw [hheight z hz]; congr 1; ring
         _ ≤ |X z 2|+|b| := abs_sub _ _
         _ ≤ M := by dsimp [M]; linarith [hv 2]
  have hzre : z.re ∈ Icc (-M) M := abs_le.mp hx
  have hbase : ∀ ε ∈ ({-1,1} : Set ℝ),
      |X ((z.re : ℂ)+I*(ε*Y)) 0| ≤ Cp+Cm ∧ |X ((z.re : ℂ)+I*(ε*Y)) 1| ≤ Cp+Cm := by
    intro ε hε
    rcases (show ε = -1 ∨ ε = 1 by simpa using hε) with rfl | rfl
    · have hb := hmBound _ ⟨z.re,hzre,rfl⟩
      have hj (j : Fin 3) : |X ((z.re : ℂ)+I*(-Y)) j| ≤ Cp+Cm := by
        have h := (norm_le_pi_norm (X ((z.re : ℂ)+I*(-Y))) j).trans hb
        simp only [Real.norm_eq_abs] at h
        linarith
      simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul] using And.intro (hj 0) (hj 1)
    · have hb := hpBound _ ⟨z.re,hzre,rfl⟩
      have hj (j : Fin 3) : |X ((z.re : ℂ)+I*Y) j| ≤ Cp+Cm := by
        have h := (norm_le_pi_norm (X ((z.re : ℂ)+I*Y)) j).trans hb
        simp only [Real.norm_eq_abs] at h
        linarith
      simpa only [Complex.ofReal_one,one_mul] using And.intro (hj 0) (hj 1)
  have hzcoord : (z.re : ℂ)+I*z.im = z := by simpa [mul_comm] using Complex.re_add_im z
  have hy := height_end_vertical_escape_bound α z.re R₀ Y B (Cp+Cm) hY hRY hB
    (by linarith) hX hF hbase
    (y := z.im) (by rw [hzcoord]; exact hv 0) (by rw [hzcoord]; exact hv 1)
  have hn := Complex.norm_le_abs_re_add_abs_im z
  linarith

/-- Holomorphic corrections vanishing at infinity provide the uniform
small-phase bound required by the spatial escape estimate. -/
theorem helicoidal_correction_small_phase {F : ℂ → ℂ}
    (hF : Tendsto F (cobounded ℂ) (𝓝 0)) (R₀ : ℝ) :
    ∃ Y : ℝ, 0 < Y ∧ R₀ < Y ∧ ∀ z : ℂ, Y ≤ ‖z‖ → |(F z).im| ≤ 1 := by
  have he : ∀ᶠ z in cobounded ℂ, ‖F z‖ < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right] using hF.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  refine ⟨max R (max (R₀+1) 1),?_,?_,?_⟩
  · linarith [le_max_right R (max (R₀+1) 1),le_max_right (R₀+1) (1 : ℝ)]
  · linarith [le_max_right R (max (R₀+1) 1),le_max_left (R₀+1) (1 : ℝ)]
  · intro z hz
    exact (Complex.abs_im_le_norm (F z)).trans (hR ((le_max_left _ _).trans hz)).le

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_end_bounded_image_parameter_bound
