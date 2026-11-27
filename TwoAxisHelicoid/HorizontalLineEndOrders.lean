import TwoAxisHelicoid.HorizontalLineCoordinates
import TwoAxisHelicoid.TorusEndScalingOrders
import TwoAxisHelicoid.CoordinateOrientationIsometry

namespace TwoAxisHelicoid
open Complex Matrix Filter
open scoped Topology ComplexConjugate

theorem lineAxisCoordinates_dist_sq (c : ℂ) (hc : ‖c‖ = 1) (A v w : Fin 3 → ℝ) :
    (∑ j, (lineAxisCoordinates c hc A v j-lineAxisCoordinates c hc A w j)^2) = ∑ j, (v j-w j)^2 := by
  have he : lineAxisCoordinates c hc A v-lineAxisCoordinates c hc A w = verticalRotation (conj c) (v-w) := by
    change verticalRotation _ (v-A)-verticalRotation _ (w-A) = _
    rw [← map_sub]
    congr 1
    abel
  change (∑ j, ((lineAxisCoordinates c hc A v-lineAxisCoordinates c hc A w) j)^2) = _
  rw [he]
  exact verticalRotation_preserves_squared_length (c := conj c) (by simpa) (v-w)

theorem lineAxisCoordinates_coefficients (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    {X : ℂ → Fin 3 → ℝ} {z : ℂ} (hX : DifferentiableAt ℝ X z) :
    let Y := lineAxisCoordinates c hc A ∘ X
    let p := immersionComplexCoefficient X z
    immersionComplexCoefficient Y z =
      ![(c.re : ℂ)*p 0+(c.im : ℂ)*p 1,-(c.im : ℂ)*p 0+(c.re : ℂ)*p 1,p 2] := by
  let Y := lineAxisCoordinates c hc A ∘ X
  let p := immersionComplexCoefficient X z
  have hd : HasFDerivAt Y ((verticalRotation (conj c)).comp (nullRealDerivative p)) z :=
    (verticalRotation _).hasFDerivAt.comp z ((immersionComplexCoefficient_hasFDerivAt hX).sub_const A)
  have he := (immersionComplexCoefficient_hasFDerivAt hd.differentiableAt).unique hd
  funext j
  apply realCoefficientDerivative_injective
  ext u
  have hv := congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D u j) he
  change (u*immersionComplexCoefficient Y z j).re = verticalRotation (conj c) (nullRealDerivative p u) j at hv
  change (u*immersionComplexCoefficient Y z j).re = _
  rw [hv]
  fin_cases j <;> simp [realCoefficientDerivative,verticalRotation_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem lineAxisCoordinates_gauss (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    {X : ℂ → Fin 3 → ℝ} {z : ℂ} (hX : DifferentiableAt ℝ X z) :
    immersionGaussMap (lineAxisCoordinates c hc A ∘ X) z = c⁻¹*immersionGaussMap X z := by
  let p := immersionComplexCoefficient X z
  have hcoeff := lineAxisCoordinates_coefficients c hc A hX
  unfold immersionGaussMap nullGauss nullHorizontalMinus
  rw [hcoeff]
  change p 2 / ((c.re*p 0+c.im*p 1)-I*(-(c.im : ℂ)*p 0+c.re*p 1)) = c⁻¹*(p 2/(p 0-I*p 1))
  have hden : ((c.re : ℂ)*p 0+c.im*p 1)-I*(-(c.im : ℂ)*p 0+c.re*p 1) = c*(p 0-I*p 1) := by
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (norm := ring) (c.im : ℂ)*p 1*I_sq
  rw [hden,div_eq_mul_inv,mul_inv,div_eq_mul_inv]
  ring

/-- Translating the origin and rotating about the vertical direction preserve
both actual end orders. The Gauss map acquires one constant unit multiplier
which disappears from its logarithmic derivative. -/
theorem lineAxisCoordinates_end_orders (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    {X : ℂ → Fin 3 → ℝ} (hX : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ X z) :
    let Y := lineAxisCoordinates c hc A ∘ X
    meromorphicOrderAt (fun z => immersionComplexCoefficient Y z 2) 0 =
        meromorphicOrderAt (fun z => immersionComplexCoefficient X z 2) 0 ∧
      meromorphicOrderAt (immersionGaussLogDerivative Y) 0 = meromorphicOrderAt (immersionGaussLogDerivative X) 0 := by
  let Y := lineAxisCoordinates c hc A ∘ X
  have h₁ : (fun z => immersionComplexCoefficient Y z 2) =ᶠ[𝓝[≠] (0:ℂ)] (fun z => immersionComplexCoefficient X z 2) :=
    hX.mono fun z hz => congrFun (lineAxisCoordinates_coefficients c hc A hz) 2
  have h₂ := hX.mono fun z hz => lineAxisCoordinates_gauss c hc A hz
  have hn : c ≠ 0 := fun h => by simp [h] at hc
  refine ⟨meromorphicOrderAt_congr h₁,meromorphicOrderAt_congr ?_⟩
  filter_upwards [punctured_germ_eventually_local h₂] with z hz
  unfold immersionGaussLogDerivative
  rw [hz.deriv_eq,hz.self_of_nhds,deriv_const_mul_field]
  exact mul_div_mul_left _ _ (inv_ne_zero hn)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.lineAxisCoordinates_end_orders
