import TwoAxisHelicoid.WeierstrassVariationFrame
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
namespace TwoAxisHelicoid
open Complex Matrix

noncomputable def coordinateAreaDensity (X : ℂ → Fin 3 → ℝ) (z : ℂ) : ℝ :=
  let A := deriv (fun t : ℝ => X (z+(t : ℂ))) 0
  let B := deriv (fun t : ℝ => X (z+I*(t : ℂ))) 0
  Real.sqrt ((A ⬝ᵥ A)*(B ⬝ᵥ B)-(A ⬝ᵥ B)^2)

noncomputable def weierstrassNormalVariation (X : ℂ → Fin 3 → ℝ) (W : ℂ → ℂ)
    (φ : ℂ → ℝ) (s : ℝ) (z : ℂ) : Fin 3 → ℝ :=
  X z+s • (φ z • holomorphicLogGaussNormal W z)

theorem complex_line_hasDerivAt (z w : ℂ) :
    HasDerivAt (fun s : ℝ => z+(s : ℂ)*w) w 0 := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_id (0 : ℝ))).mul_const w).const_add z
  simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul,Function.comp_def,id_eq] using h

theorem complex_line_composition_hasDerivAt {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    {D : ℂ →L[ℝ] (Fin 3 → ℝ)} (hX : HasFDerivAt X D z) (w : ℂ) :
    HasDerivAt (fun s : ℝ => X (z+(s : ℂ)*w)) (D w) 0 := by
  have hX' : HasFDerivAt X D (z+((0 : ℝ) : ℂ)*w) := by simpa using hX
  exact hX'.comp_hasDerivAt 0 (complex_line_hasDerivAt z w)

theorem weierstrass_normal_variation_area_formula
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {φ : ℂ → ℝ} {z D : ℂ} {ux uy : ℝ}
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W z)) 1)) z)
    (hW : HasDerivAt W D z)
    (hφx : HasDerivAt (fun t : ℝ => φ (z+(t : ℂ))) ux 0)
    (hφy : HasDerivAt (fun t : ℝ => φ (z+I*(t : ℂ))) uy 0) :
    (fun s => coordinateAreaDensity (weierstrassNormalVariation X W φ s) z) =
      vectorNormalVariationArea
        (nullRealDerivative (weierstrassTriple (exp (W z)) 1) 1)
        (nullRealDerivative (weierstrassTriple (exp (W z)) 1) I)
        (holomorphicLogGaussNormal W z)
        (deriv (fun t : ℝ => holomorphicLogGaussNormal W (z+(t : ℂ))) 0)
        (deriv (fun t : ℝ => holomorphicLogGaussNormal W (z+I*(t : ℂ))) 0)
        (φ z) ux uy := by
  have hXx := complex_line_composition_hasDerivAt hX 1
  simp only [mul_one] at hXx
  have hXy := complex_line_composition_hasDerivAt hX I
  simp only [mul_comm (I : ℂ)] at hXy ⊢
  have hNx := holomorphicLogGaussNormal_line_hasDerivAt hW 1
  simp only [mul_one] at hNx
  have hNy := holomorphicLogGaussNormal_line_hasDerivAt hW I
  simp only [mul_comm (I : ℂ)] at hφy
  have hx (s : ℝ) := HasDerivAt.add hXx ((hφx.smul hNx).const_smul s)
  have hy (s : ℝ) := HasDerivAt.add hXy ((hφy.smul hNy).const_smul s)
  funext s
  unfold coordinateAreaDensity
  have hdx := (hx s).deriv
  have hdy := (hy s).deriv
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at hdx hdy
  change deriv (fun t : ℝ => weierstrassNormalVariation X W φ s (z+(t : ℂ))) 0 = _ at hdx
  change deriv (fun t : ℝ => weierstrassNormalVariation X W φ s (z+(t : ℂ)*I)) 0 = _ at hdy
  simp only [mul_comm (I : ℂ)]
  rw [hdx,hdy]
  unfold vectorNormalVariationArea
  rw [hNx.deriv,hNy.deriv]
  dsimp only
  simp only [add_comm]

/-- Pointwise second variation of the area density of the actual maps
X_s=X+s φ N, with the Weierstrass differential and holomorphic Gauss map.
This is a proved area calculation, not a second-variation axiom. -/
theorem actual_weierstrass_normal_area_second_variation
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {φ : ℂ → ℝ} {z D : ℂ} {ux uy : ℝ}
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W z)) 1)) z)
    (hW : HasDerivAt W D z)
    (hφx : HasDerivAt (fun t : ℝ => φ (z+(t : ℂ))) ux 0)
    (hφy : HasDerivAt (fun t : ℝ => φ (z+I*(t : ℂ))) uy 0) :
    HasDerivAt (deriv (fun s => coordinateAreaDensity (weierstrassNormalVariation X W φ s) z))
      (ux^2+uy^2-(2*‖D‖^2/(Real.cosh (W z).re)^2)*(φ z)^2) 0 := by
  rw [weierstrass_normal_variation_area_formula hX hW hφx hφy]
  exact weierstrass_vector_normal_area_second_variation hW (φ z) ux uy

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_weierstrass_normal_area_second_variation
