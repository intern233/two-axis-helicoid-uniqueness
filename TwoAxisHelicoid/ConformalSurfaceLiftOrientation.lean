import TwoAxisHelicoid.ConformalPlaneColumns

namespace TwoAxisHelicoid
open Complex Matrix Set Filter
open scoped Topology

/-- In regular conformal surface charts, the lift of a spatial similarity
has a conformal real derivative. Its orientation is determined by the
two columns, and the first column never vanishes. -/
theorem lifted_similarity_plane_columns {Y : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    {R : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {z : ℂ}
    (hY : DifferentiableAt ℝ Y z) (hY' : DifferentiableAt ℝ Y (F z))
    (hc : ConformalCoordinateDerivatives Y z) (hc' : ConformalCoordinateDerivatives Y (F z))
    (hi : Function.Injective (fderiv ℝ Y z)) (hi' : Function.Injective (fderiv ℝ Y (F z)))
    (hF : DifferentiableAt ℝ F z) {P : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    (hR : HasFDerivAt R P (Y z)) {k : ℝ} (hk : 0 < k)
    (hmetric : ∀ u v, P u ⬝ᵥ P v = k*(u ⬝ᵥ v))
    (he : Y ∘ F =ᶠ[𝓝 z] R ∘ Y) :
    fderiv ℝ F z 1 ≠ 0 ∧
      (fderiv ℝ F z I = I*fderiv ℝ F z 1 ∨ fderiv ℝ F z I = -(I*fderiv ℝ F z 1)) := by
  let D := fderiv ℝ Y z
  let C := fderiv ℝ Y (F z)
  let G := fderiv ℝ F z
  have half (x : Fin 3 → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)) (fun h => hx (dotProduct_self_eq_zero.mp h.symm))
  have hg : 0 < C 1 ⬝ᵥ C 1 := half _ (fun h => one_ne_zero (hi' (h.trans C.map_zero.symm)))
  have hg' : 0 < D 1 ⬝ᵥ D 1 := half _ (fun h => one_ne_zero (hi (h.trans D.map_zero.symm)))
  have hd := ((hY'.hasFDerivAt.comp z hF.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    (hR.comp z hY.hasFDerivAt)
  have hd' (v : ℂ) : C (G v) = P (D v) := congrArg (fun T : ℂ →L[ℝ] (Fin 3 → ℝ) => T v) hd
  obtain ⟨h1,h2⟩ := (conformalCoordinateDerivatives_iff_dot hY).mp hc
  obtain ⟨h1',h2'⟩ := (conformalCoordinateDerivatives_iff_dot hY').mp hc'
  have hh (u v : ℂ) : (C 1 ⬝ᵥ C 1)*((G u).re*(G v).re+(G u).im*(G v).im) = k*(D u ⬝ᵥ D v) := by
    rw [← spatial_conformal_pairing C h1' h2',hd',hd',hmetric]
  have hn : G 1 ≠ 0 := by
    intro h
    have hnorm := hh 1 1
    rw [h] at hnorm
    simp only [zero_re,zero_im,add_zero,mul_zero] at hnorm
    exact (mul_pos hk hg').ne' hnorm.symm
  refine ⟨hn,perpendicular_equal_columns hn ?_ ?_⟩
  · apply mul_left_cancel₀ hg.ne'
    exact (hh 1 1).trans ((congrArg (k*·) h1).trans (hh I I).symm)
  · apply (mul_eq_zero.mp ?_).resolve_left hg.ne'
    change D 1 ⬝ᵥ D I = 0 at h2
    exact (hh 1 I).trans (by rw [h2,mul_zero])

/-- Composing the same real conformal orientation twice produces a complex
linear derivative on the full open domain. -/
theorem conformal_plane_square_holomorphic {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) {F : ℂ → ℂ} (hF : AnalyticOnNhd ℝ F U)
    (hmap : MapsTo F U U)
    (hcol : ∀ z ∈ U, fderiv ℝ F z 1 ≠ 0 ∧
      (fderiv ℝ F z I = I*fderiv ℝ F z 1 ∨ fderiv ℝ F z I = -(I*fderiv ℝ F z 1))) :
    AnalyticOnNhd ℂ (F ∘ F) U := by
  let D := fderiv ℝ F
  have hcont (v : ℂ) : ContinuousOn (fun z => D z v) U := fun z hz =>
    (((ContinuousLinearMap.apply ℝ ℂ v).analyticAt _).comp (hF z hz).fderiv).continuousAt.continuousWithinAt
  obtain hplus | hminus := constant_conformal_column_sign hconn (hcont I) (continuousOn_const.mul (hcont 1))
    (fun w hw => mul_ne_zero I_ne_zero (hcol w hw).1) (fun z hz => (hcol z hz).2)
  all_goals
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hG := (hF (F z) (hmap hz)).differentiableAt.hasFDerivAt.comp z (hF z hz).differentiableAt.hasFDerivAt
    apply ((complex_differentiable_iff_columns hG.differentiableAt).mpr ?_).differentiableWithinAt
    rw [hG.fderiv]
    change D (F z) (D z I) = I*D (F z) (D z 1)
  · change ∀ z ∈ U, D z I = I*D z 1 at hplus
    rw [hplus z hz,real_complex_map_intertwines (D (F z)) (Or.inl rfl) (hplus _ (hmap hz))]
  · change ∀ z ∈ U, D z I = -(I*D z 1) at hminus
    rw [hminus z hz,map_neg,real_complex_map_intertwines (D (F z)) (Or.inr rfl) (by simpa using hminus _ (hmap hz))]
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conformal_plane_square_holomorphic
