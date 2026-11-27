import TwoAxisHelicoid.NormalVariationFrame
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.CrossProduct

namespace TwoAxisHelicoid
open Matrix

/-- The two conformal tangent vectors and a unit normal test all three
components of a spatial vector. -/
theorem conformal_triple_orthogonal_zero {A B n W : Fin 3 → ℝ} {g : ℝ}
    (hg : 0 < g) (haa : A ⬝ᵥ A = g) (hbb : B ⬝ᵥ B = g) (hab : A ⬝ᵥ B = 0)
    (hnn : n ⬝ᵥ n = 1) (hna : n ⬝ᵥ A = 0) (hnb : n ⬝ᵥ B = 0)
    (hwA : A ⬝ᵥ W = 0) (hwB : B ⬝ᵥ W = 0) (hwn : n ⬝ᵥ W = 0) : W = 0 := by
  let T : Matrix (Fin 3) (Fin 3) ℝ := ![A,B,n]
  have hba : B ⬝ᵥ A = 0 := (dotProduct_comm _ _).trans hab
  have han : A ⬝ᵥ n = 0 := (dotProduct_comm _ _).trans hna
  have hbn : B ⬝ᵥ n = 0 := (dotProduct_comm _ _).trans hnb
  have hM : T * T.transpose = diagonal ![g,g,1] := by
    ext i j
    change T i ⬝ᵥ T j = diagonal _ i j
    fin_cases i <;> fin_cases j <;> simp [T,diagonal,haa,hbb,hab,hba,han,hbn,hna,hnb,hnn]
  have hm : T.det ≠ 0 := by
    intro hd
    have h := congrArg Matrix.det hM
    simp [det_mul,hd,det_diagonal,Fin.prod_univ_succ,hg.ne'] at h
  by_contra hw
  apply hm
  apply (Matrix.exists_mulVec_eq_zero_iff (M := T)).mp
  refine ⟨W,hw,?_⟩
  ext i
  fin_cases i
  · exact hwA
  · exact hwB
  · exact hwn

/-- The Weingarten derivatives in a conformal minimal chart have a
symmetric traceless matrix, written here on the actual spatial vectors. -/
theorem ConformalNormalFrame.scaled_normal_columns {A B n nx ny : Fin 3 → ℝ} {g b c : ℝ}
    (H : ConformalNormalFrame A B n nx ny g b c) :
    g • nx = (-b) • A + (-c) • B ∧ g • ny = (-c) • A + b • B := by
  have ha : A ⬝ᵥ nx = -b := (dotProduct_comm _ _).trans H.nxa
  have hb : B ⬝ᵥ nx = -c := (dotProduct_comm _ _).trans H.nxb
  have hc : A ⬝ᵥ ny = -c := (dotProduct_comm _ _).trans H.nya
  have hd : B ⬝ᵥ ny = b := (dotProduct_comm _ _).trans H.nyb
  have hba := (dotProduct_comm B A).trans H.ab
  constructor <;> apply sub_eq_zero.mp <;>
    apply conformal_triple_orthogonal_zero H.metric_pos H.aa H.bb H.ab H.nn H.na H.nb <;>
    simp only [dotProduct_sub,dotProduct_add,dotProduct_smul,smul_eq_mul,ha,hb,hc,hd,H.nnx,H.nny,
      H.na,H.nb,H.aa,H.bb,H.ab,hba,mul_zero,zero_add,add_zero] <;> ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ConformalNormalFrame.scaled_normal_columns
