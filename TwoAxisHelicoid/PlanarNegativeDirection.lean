import TwoAxisHelicoid.SchrodingerTensorEnergy

namespace TwoAxisHelicoid
open MeasureTheory Filter
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem lineMass_positive_of_nonzero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) {x : ℝ} (hx : f x ≠ 0) : 0 < lineMass f :=
  integral_pos_of_integrable_nonneg_nonzero (hf.continuous.pow 2)
    (smooth_compact_square_integrable hf hs) (fun y => sq_nonneg (f y)) (pow_ne_zero 2 hx)

/-- Dilation in the free direction makes the tensor product of a compact
negative one-dimensional test function into an actual compact negative
two-dimensional test function. -/
theorem exists_planar_smooth_compact_negative_direction {V : ℝ → ℝ}
    (hV : Continuous V) (hn : ∀ x, 0 ≤ V x) (hp : 0 < V 0) :
    ∃ v : ℝ × ℝ → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      planarSchrodingerEnergy V v < 0 := by
  obtain ⟨ψ,hψ,hψs,hq⟩ := exists_smooth_compact_negative_direction hV hn hp
  let χ : ContDiffBump (0 : ℝ) := default
  have hχ : ContDiff ℝ ∞ χ := χ.contDiff
  have hχmass : 0 < lineMass χ := lineMass_positive_of_nonzero hχ χ.hasCompactSupport
    (show χ 0 ≠ 0 by rw [χ.eventuallyEq_one.self_of_nhds]; norm_num)
  change lineSchrodingerEnergy V ψ < 0 at hq
  let a := -lineMass χ*lineSchrodingerEnergy V ψ
  have ha : 0 < a := by dsimp [a]; nlinarith
  let b := lineDirichletEnergy χ*lineMass ψ
  obtain ⟨R,hRbig⟩ := exists_gt (max (1 : ℝ) (b/a))
  have hR1 : 1 < R := (le_max_left _ _).trans_lt hRbig
  have hR : 0 < R := by linarith
  have hbR : b < R*a := (div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hRbig)
  have hR2 : R < R^2 := by nlinarith
  have hnegative : b/R-R*a < 0 := by
    have hbR2 : b < R^2*a := hbR.trans (mul_lt_mul_of_pos_right hR2 ha)
    apply (mul_lt_mul_iff_right₀ hR).mp
    rw [mul_zero]
    have he : R*(b/R-R*a) = b-R^2*a := by field_simp
    rw [he]
    linarith
  let f : ℝ → ℝ := fun x => χ (x/R)
  obtain ⟨hf,hfs⟩ := smooth_compact_dilate hχ χ.hasCompactSupport hR
  obtain ⟨hv,hvs⟩ := smooth_compact_tensor hf hψ hfs hψs
  refine ⟨fun p => f p.1*ψ p.2,hv,hvs,?_⟩
  rw [planarSchrodingerEnergy_tensor hV hf hψ hfs hψs,
    lineDirichletEnergy_dilate (hχ.differentiable (by simp)) hR,lineMass_dilate χ hR]
  convert hnegative using 1
  dsimp [a,b]
  ring

theorem exists_helicoid_planar_smooth_compact_negative_direction :
    ∃ v : ℝ × ℝ → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      planarSchrodingerEnergy (fun t => 2*helicoidGroundState t^2) v < 0 := by
  apply exists_planar_smooth_compact_negative_direction
  · unfold helicoidGroundState
    fun_prop (disch := intros; positivity)
  · intro x; positivity
  · norm_num [helicoidGroundState]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_planar_smooth_compact_negative_direction
#print axioms TwoAxisHelicoid.exists_helicoid_planar_smooth_compact_negative_direction
