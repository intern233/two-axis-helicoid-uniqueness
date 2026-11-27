import TwoAxisHelicoid.TorusQuaternionLiftCriterion
import TwoAxisHelicoid.SpatialGramFrames
import TwoAxisHelicoid.DiskBoundarySpinHomotopy
import TwoAxisHelicoid.EssentialPlanarTurning

namespace TwoAxisHelicoid
open Complex Set

/-- Varying the tangent direction through a periodic homotopy of nonzero
vectors preserves the lift test on the actual Euclidean Gram frames,
including for a non-conformal parametrization. -/
theorem regular_frame_closed_of_direction_homotopy
    (D : C(unitInterval,ℂ →L[ℝ] (Fin 3 → ℝ))) (hi : ∀ t, Function.Injective (D t))
    (hp : D 1 = D 0) (V : C(unitInterval × unitInterval,ℂ))
    (hv : ∀ z, V z ≠ 0) (hper : ∀ s : unitInterval, V (s,1) = V (s,0))
    (hstart : SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hi t) (hv (0,t)))) :
    SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hi t) (hv (1,t))) := by
  let H : C(unitInterval × unitInterval,OrthonormalTangentPair) :=
    ⟨fun z => spatialDifferentialFrame (hi z.2) (hv z),
      spatialDifferentialFrame_continuous (D.continuous.comp continuous_snd) V.continuous _ _⟩
  have he (s : unitInterval) : H (s,1) = H (s,0) := by
    apply Subtype.ext
    change spatialGramFrame (D 1 (V (s,1))) (D 1 (I*V (s,1))) = spatialGramFrame (D 0 (V (s,0))) (D 0 (I*V (s,0)))
    rw [hp,hper]
  obtain ⟨q,hqc,hq⟩ := hstart
  obtain ⟨r,hr,hrc⟩ := quaternion_loop_closed_lift_homotopy H he q hq hqc
  exact ⟨r,hrc,hr⟩

theorem regular_frame_closed_change_constant
    (D : C(unitInterval,ℂ →L[ℝ] (Fin 3 → ℝ))) (hi : ∀ t, Function.Injective (D t))
    (hp : D 1 = D 0) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hi t) ha)) :
    SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hi t) hb) := by
  have hpc : IsPathConnected ({0}ᶜ : Set ℂ) := isPathConnected_compl_singleton_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ) 0
  obtain ⟨v,hv⟩ := hpc.joinedIn a ha b hb
  let V : C(unitInterval × unitInterval,ℂ) := ⟨fun z => v z.1,v.continuous.comp continuous_fst⟩
  have hn (z) : V z ≠ 0 := hv z.1
  have h0 (t : unitInterval) : spatialDifferentialFrame (hi t) (hn (0,t)) =
      spatialDifferentialFrame (hi t) ha := by
    apply Subtype.ext
    simp [V,spatialDifferentialFrame]
  have h1 (t : unitInterval) : spatialDifferentialFrame (hi t) (hn (1,t)) =
      spatialDifferentialFrame (hi t) hb := by
    apply Subtype.ext
    simp [V,spatialDifferentialFrame]
  simpa only [h1] using regular_frame_closed_of_direction_homotopy D hi hp V hn (fun _ => rfl)
    (by simpa only [h0] using h)

theorem essential_frame_closed_of_fixed_direction
    {ξ : ℝ → ℂ} (hξ : ContDiff ℝ 1 ξ) {ω : ℂ} (hω : ω ≠ 0)
    (hp : ∀ t, ξ (t+1) = ξ t+ω) (hr : ∀ t, deriv ξ t ≠ 0)
    (hinj : ∀ t h : ℝ, h ∈ Ioo (0:ℝ) 1 → ξ (t+h) ≠ ξ t)
    (D : C(unitInterval,ℂ →L[ℝ] (Fin 3 → ℝ))) (hi : ∀ t, Function.Injective (D t))
    (hDp : D 1 = D 0)
    (h : SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hi t) (v := 1) one_ne_zero)) :
    SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hi t) (hr t.1)) := by
  have hωc := regular_frame_closed_change_constant D hi hDp one_ne_zero hω h
  obtain ⟨V,hn,h0,h1,hper⟩ := essential_torus_velocity_homotopy hξ hω hp hr hinj
  have e0 (t : unitInterval) : spatialDifferentialFrame (hi t) (hn (0,t)) = spatialDifferentialFrame (hi t) hω := by
    apply Subtype.ext
    simp only [spatialDifferentialFrame,h0]
  have e1 (t : unitInterval) : spatialDifferentialFrame (hi t) (hn (1,t)) = spatialDifferentialFrame (hi t) (hr t.1) := by
    apply Subtype.ext
    simp only [spatialDifferentialFrame,h1]
  simpa only [e1] using regular_frame_closed_of_direction_homotopy D hi hDp V hn hper
    (by simpa only [e0] using hωc)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.essential_frame_closed_of_fixed_direction
