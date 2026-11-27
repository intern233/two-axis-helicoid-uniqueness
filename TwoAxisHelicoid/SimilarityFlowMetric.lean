import TwoAxisHelicoid.AffineAmbientFlow
import TwoAxisHelicoid.ImmersedSimilarityRigidity
import TwoAxisHelicoid.ConformalCoordinateLaplacian

namespace TwoAxisHelicoid
open Matrix

theorem similarityLinear_inner_deriv (b : Fin 3 → ℝ) (d : ℝ) (u v : Fin 3 → ℝ) :
    similarityLinear b d u ⬝ᵥ v + u ⬝ᵥ similarityLinear b d v = 2*d*(u ⬝ᵥ v) := by
  have h₁ : (b ⨯₃ u) ⬝ᵥ v = b ⬝ᵥ (u ⨯₃ v) := (dotProduct_comm _ _).trans (triple_product_permutation v b u)
  have h₂ : u ⬝ᵥ (b ⨯₃ v) = -(b ⬝ᵥ (u ⨯₃ v)) := by
    rw [triple_product_permutation u b v,← cross_anticomm u v,dotProduct_neg]
  simp only [similarityLinear_apply,add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,h₁,h₂]
  ring

/-- The derivative in the spatial variable of the complete affine flow
scales every inner product by exp(2dt). -/
theorem similarity_flow_metric (a b : Fin 3 → ℝ) (d t : ℝ) (u v : Fin 3 → ℝ) :
    affineAmbientLinearPart (similarityLinear b d) a t u ⬝ᵥ affineAmbientLinearPart (similarityLinear b d) a t v =
      Real.exp (2*d*t)*(u ⬝ᵥ v) := by
  let L := similarityLinear b d
  let P := affineAmbientLinearPart L a
  let h := fun s => P s u ⬝ᵥ P s v
  have hd (s : ℝ) : HasDerivAt h (2*d*h s) s := by
    have hh := real_vector_dot_hasDerivAt (affineAmbientLinearPart_deriv L a u s) (affineAmbientLinearPart_deriv L a v s)
    simpa only [L,similarityLinear_inner_deriv] using hh
  let f := fun s => Real.exp (-(2*d)*s)*h s
  have hf (s : ℝ) : HasDerivAt f 0 s := by
    have he := ((hasDerivAt_id s).const_mul (-(2*d))).exp.mul (hd s)
    change HasDerivAt f (Real.exp (-(2*d)*s)*(-(2*d)*1)*h s+Real.exp (-(2*d)*s)*(2*d*h s)) s at he
    convert he using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt) (fun s => (hf s).deriv) t 0
  have hzero (w : Fin 3 → ℝ) : P 0 w = w := congrArg Prod.fst (homogeneousFlow_zero L a (w,0))
  change Real.exp (-(2*d)*t)*h t = Real.exp (-(2*d)*0)*(P 0 u ⬝ᵥ P 0 v) at hc
  rw [mul_zero,Real.exp_zero,one_mul,hzero,hzero,neg_mul,Real.exp_neg] at hc
  change h t = _
  calc
    h t = Real.exp (2*d*t)*(Real.exp (2*d*t))⁻¹*h t := by rw [mul_inv_cancel₀ (Real.exp_pos _).ne',one_mul]
    _ = _ := by rw [mul_assoc,hc]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.similarity_flow_metric
