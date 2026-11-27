import TwoAxisHelicoid.AsymptoticAxisCone
import TwoAxisHelicoid.AxisHelicoidThin

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

private theorem translated_cone_distance (v b : Fin 3 → ℝ) {κ θ : ℝ}
    (hκ : 0 ≤ κ) (hb₀ : |b 0| ≤ κ) (hb₁ : |b 1| ≤ κ) (hb₂ : b 2 = 0) (hv : v 2 = θ)
    (hcone : |endHorizontalTransverse θ (v-b)| ≤ κ*|endHorizontalSupport θ (v-b)|) :
    ∃ r φ : ℝ, helicoidSquaredDistance
      (verticalRotation I v 0,verticalRotation I v 1,verticalRotation I v 2) r φ ≤ (3*κ)^2 := by
  let V := verticalRotation I v
  let W := verticalRotation I (v-b)
  have hw : (v-b) 2 = θ := by simp [hv,hb₂]
  have coord := quarter_rotated_horizontal_cone_coordinates (v-b) θ hw
  obtain ⟨r,φ,h⟩ := horizontal_cone_helicoid_distance hκ hcone
  let pt := fun w : Fin 3 → ℝ => helicoidEuclideanPoint (w 0,w 1,w 2)
  have hnear : dist (pt W) (euclideanHelicoid r φ) ≤ κ := by
    apply (sq_le_sq₀ dist_nonneg hκ).mp
    rw [← helicoidSquaredDistance_eq_euclidean_dist]
    have ex := congrArg (fun a : HelicoidTubeCoordinates => (a.1.1,a.1.2,a.2)) coord
    change (W 0,W 1,W 2) = _ at ex
    rwa [ex]
  have hdelta : dist (pt V) (pt W)^2 = (b 0)^2+(b 1)^2 := by
    rw [dist_eq_norm,EuclideanSpace.real_norm_sq_eq]
    simp [pt,V,W,verticalRotation_apply,helicoidEuclideanPoint,Fin.sum_univ_succ,hb₂]
    ring
  have small : dist (pt V) (pt W) ≤ 2*κ := by
    apply (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ 2*κ)).mp
    rw [hdelta]
    nlinarith [sq_le_sq' (abs_le.mp hb₀).1 (abs_le.mp hb₀).2,
      sq_le_sq' (abs_le.mp hb₁).1 (abs_le.mp hb₁).2,sq_nonneg κ]
  refine ⟨r,φ,?_⟩
  rw [helicoidSquaredDistance_eq_euclidean_dist]
  exact (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ 3*κ)).mpr
    ((dist_triangle (pt V) (pt W) _).trans (by linarith))

/-- A common limiting horizontal center suffices for every far point to lie
inside arbitrarily thin genuine Euclidean normal tubes of the helicoid. -/
theorem height_end_asymptotic_axis_arbitrarily_thin {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} (R : ℝ)
    (hX : ∀ z : ℂ, R < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*z+F z)) 1)) z)
    (hheight : ∀ z : ℂ, R < ‖z‖ → X z 2 = z.re)
    (hF : Tendsto F (cobounded ℂ) (𝓝 0))
    (h₀ : Tendsto (fun x : ℝ => X (x:ℂ) 0) (cobounded ℝ) (𝓝 0))
    (h₁ : Tendsto (fun x : ℝ => X (x:ℂ) 1) (cobounded ℝ) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ z : ℂ, S < ‖z‖ →
      coordinateToTube (verticalRotation I (X z)) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance (coordinateToTube (verticalRotation I (X z)))| ≤ ε := by
  intro ε hε
  let κ := min (ε/3) (1/6)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have kε : 3*κ ≤ ε := by dsimp [κ]; linarith [min_le_left (ε/3) (1/6 : ℝ)]
  have k1 : 3*κ < 1 := by dsimp [κ]; linarith [min_le_right (ε/3) (1/6 : ℝ)]
  obtain ⟨T,_,hT⟩ := height_end_asymptotic_axis_cones 1 R
    (by simpa only [Complex.ofReal_one,mul_one] using hX) hF h₀ h₁ κ κ hκ hκ
  refine ⟨max T R,?_⟩
  intro z hz
  obtain ⟨b,hb₀,hb₁,hb₂,hc⟩ := hT z ((le_max_left _ _).trans_lt hz)
  simp only [one_mul] at hc
  have hd := translated_cone_distance (X z) b hκ.le hb₀ hb₁ hb₂
    (hheight z ((le_max_right _ _).trans_lt hz)) hc
  have h := helicoid_tube_of_squared_distance_le
    (y := coordinateToTube (verticalRotation I (X z))) (by positivity : 0 ≤ 3*κ) k1 hd
  exact ⟨h.1,h.2.trans kε⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_end_asymptotic_axis_arbitrarily_thin
