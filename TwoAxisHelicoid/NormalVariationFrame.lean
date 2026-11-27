import TwoAxisHelicoid.ConformalAreaVariation
import Mathlib.Data.Matrix.Mul

set_option autoImplicit false
namespace TwoAxisHelicoid
open Matrix

/-- Pointwise first and second fundamental identities in conformal minimal
coordinates, written as identities of actual ambient vectors. -/
structure ConformalNormalFrame (A B n nx ny : Fin 3 → ℝ) (g b c : ℝ) : Prop where
  metric_pos : 0 < g
  aa : A ⬝ᵥ A = g
  bb : B ⬝ᵥ B = g
  ab : A ⬝ᵥ B = 0
  nn : n ⬝ᵥ n = 1
  na : n ⬝ᵥ A = 0
  nb : n ⬝ᵥ B = 0
  nnx : n ⬝ᵥ nx = 0
  nny : n ⬝ᵥ ny = 0
  nxnx : nx ⬝ᵥ nx = (b^2+c^2)/g
  nyny : ny ⬝ᵥ ny = (b^2+c^2)/g
  nxny : nx ⬝ᵥ ny = 0
  nxa : nx ⬝ᵥ A = -b
  nxb : nx ⬝ᵥ B = -c
  nya : ny ⬝ᵥ A = -c
  nyb : ny ⬝ᵥ B = b

noncomputable def vectorNormalVariationArea
    (A B n nx ny : Fin 3 → ℝ) (u ux uy s : ℝ) : ℝ :=
  let U := A+s • (ux • n+u • nx)
  let V := B+s • (uy • n+u • ny)
  Real.sqrt ((U ⬝ᵥ U)*(V ⬝ᵥ V)-(U ⬝ᵥ V)^2)

theorem vectorNormalVariationArea_formula {A B n nx ny : Fin 3 → ℝ} {g b c : ℝ}
    (h : ConformalNormalFrame A B n nx ny g b c) (u ux uy : ℝ) :
    vectorNormalVariationArea A B n nx ny u ux uy = normalVariationArea g b c u ux uy := by
  have han : A ⬝ᵥ n = 0 := (dotProduct_comm A n).trans h.na
  have hbn : B ⬝ᵥ n = 0 := (dotProduct_comm B n).trans h.nb
  have hnxn : nx ⬝ᵥ n = 0 := (dotProduct_comm nx n).trans h.nnx
  have hnyn : ny ⬝ᵥ n = 0 := (dotProduct_comm ny n).trans h.nny
  have hanx : A ⬝ᵥ nx = -b := (dotProduct_comm A nx).trans h.nxa
  have hbny : B ⬝ᵥ ny = b := (dotProduct_comm B ny).trans h.nyb
  have hany : A ⬝ᵥ ny = -c := (dotProduct_comm A ny).trans h.nya
  have hnxb : nx ⬝ᵥ B = -c := h.nxb
  funext s
  unfold vectorNormalVariationArea normalVariationArea
  dsimp only
  congr 1
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    h.aa,h.bb,h.ab,h.nn,h.na,h.nb,h.nnx,h.nny,h.nxnx,h.nyny,h.nxny,
    h.nxa,h.nyb,han,hbn,hnxn,hnyn,hanx,hbny,hany,hnxb]
  ring

/-- The actual vector Gram determinant has the expected second area
variation, derived from the algebraic Gram identities and scalar calculus. -/
theorem vector_normal_area_second_variation {A B n nx ny : Fin 3 → ℝ} {g b c : ℝ}
    (h : ConformalNormalFrame A B n nx ny g b c) (u ux uy : ℝ) :
    HasDerivAt (deriv (vectorNormalVariationArea A B n nx ny u ux uy))
      (ux^2+uy^2-(2*(b^2+c^2)/g)*u^2) 0 := by
  rw [vectorNormalVariationArea_formula h]
  exact conformal_normal_area_second_variation h.metric_pos b c u ux uy

end TwoAxisHelicoid
