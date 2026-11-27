import TwoAxisHelicoid.SimilaritySymmetry
import TwoAxisHelicoid.WeierstrassRotation
import TwoAxisHelicoid.UniqueAsymptoticVerticalAxis
import TwoAxisHelicoid.MinimalChartComplexData

namespace TwoAxisHelicoid
open Complex Matrix Set Filter InnerProductSpace
open scoped Topology ComplexConjugate

theorem verticalRotation_unit_inverse (c : ℂ) (hc : ‖c‖ = 1) (v : Fin 3 → ℝ) :
    verticalRotation (conj c) (verticalRotation c v) = v := by
  have hn : c.re^2+c.im^2 = 1 := by
    have h := Complex.normSq_eq_norm_sq c
    rw [hc] at h
    simpa only [Complex.normSq_apply,one_pow,pow_two,one_mul] using h
  ext j
  fin_cases j
  · change c.re*(c.re*v 0-c.im*v 1)-(-c.im)*(c.im*v 0+c.re*v 1) = v 0
    linear_combination v 0*hn
  · change (-c.im)*(c.re*v 0-c.im*v 1)+c.re*(c.im*v 0+c.re*v 1) = v 1
    linear_combination v 1*hn
  · rfl

noncomputable def unitVerticalRotation (c : ℂ) (hc : ‖c‖ = 1) : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) where
  toFun := verticalRotation c
  invFun := verticalRotation (conj c)
  map_add' := (verticalRotation c).map_add
  map_smul' := (verticalRotation c).map_smul
  left_inv := verticalRotation_unit_inverse c hc
  right_inv := fun v => by simpa using verticalRotation_unit_inverse (conj c) (by simpa) v
  continuous_toFun := (verticalRotation c).continuous
  continuous_invFun := (verticalRotation (conj c)).continuous

theorem verticalRotation_preserves_dot {c : ℂ} (hc : ‖c‖ = 1) (u v : Fin 3 → ℝ) :
    verticalRotation c u ⬝ᵥ verticalRotation c v = u ⬝ᵥ v := by
  have h w : verticalRotation c w ⬝ᵥ verticalRotation c w = w ⬝ᵥ w := by
    simpa only [dotProduct,← pow_two] using verticalRotation_preserves_squared_length hc w
  have h' := h (u+v)
  rw [map_add,add_dotProduct,dotProduct_add,dotProduct_add,add_dotProduct,dotProduct_add,dotProduct_add,
    h u,h v,dotProduct_comm (verticalRotation c v) _,dotProduct_comm v u] at h'
  linarith

/-- Euclidean coordinates centered at the chosen horizontal line. Its unit
direction is sent to the real horizontal axis while vertical directions
remain vertical. -/
noncomputable def lineAxisCoordinates (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ) :
    (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) where
  toFun := fun P => verticalRotation (conj c) (P-A)
  invFun := fun P => verticalRotation c P+A
  left_inv := fun P => by
    have h := verticalRotation_unit_inverse (conj c) (by simpa) (P-A)
    simp only [starRingEnd_self_apply] at h
    change verticalRotation c (verticalRotation (conj c) (P-A))+A = P
    rw [h,sub_add_cancel]
  right_inv := fun P => by
    change verticalRotation (conj c) (verticalRotation c P+A-A) = P
    rw [add_sub_cancel_right,verticalRotation_unit_inverse c hc]
  continuous_toFun := (verticalRotation _).continuous.comp (continuous_id.sub continuous_const)
  continuous_invFun := (verticalRotation _).continuous.add continuous_const

theorem lineAxisCoordinates_line (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ) (r : ℝ) :
    lineAxisCoordinates c hc A (A+r • ![c.re,c.im,0]) = ![r,0,0] := by
  have hu : verticalRotation c (![r,0,0] : Fin 3 → ℝ) = r • ![c.re,c.im,0] := by
    ext j
    fin_cases j <;> simp [verticalRotation_apply] <;> ring
  change verticalRotation (conj c) (_-A) = _
  rw [add_sub_cancel_left,← hu,verticalRotation_unit_inverse c hc]

theorem lineAxisCoordinates_half_turn (c : ℂ) (hc : ‖c‖ = 1) (A P : Fin 3 → ℝ) :
    lineAxisCoordinates c hc A (horizontalLineHalfTurn A ![c.re,c.im,0] P) =
      halfTurnX (lineAxisCoordinates c hc A P) := by
  have hn : c.re^2+c.im^2 = 1 := by
    have h := Complex.normSq_eq_norm_sq c
    rw [hc] at h
    simpa only [Complex.normSq_apply,one_pow,pow_two,one_mul] using h
  let u := P 0-A 0
  let v := P 1-A 1
  have hd : (P-A) ⬝ᵥ ![c.re,c.im,0] = u*c.re+v*c.im := by
    simp [dotProduct,Fin.sum_univ_succ,u,v]
  unfold horizontalLineHalfTurn
  rw [hd]
  ext j
  fin_cases j
  · change c.re*(A 0+(2*(u*c.re+v*c.im))*c.re-u-A 0)-(-c.im)*(A 1+(2*(u*c.re+v*c.im))*c.im-v-A 1) = c.re*u-(-c.im)*v
    linear_combination 2*(u*c.re+v*c.im)*hn
  · change (-c.im)*(A 0+(2*(u*c.re+v*c.im))*c.re-u-A 0)+c.re*(A 1+(2*(u*c.re+v*c.im))*c.im-v-A 1) = -((-c.im)*u+c.re*v)
    ring
  · change A 2+2*(u*c.re+v*c.im)*0-(P 2-A 2)-A 2 = -(P 2-A 2)
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.lineAxisCoordinates_half_turn
