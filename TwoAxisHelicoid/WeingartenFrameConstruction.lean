import TwoAxisHelicoid.ConformalJacobiFrame

namespace TwoAxisHelicoid
open Matrix

/-- On an orthogonal tangent frame, the normal with its first derivatives
already determines their full Gram matrix from the second fundamental form. -/
theorem weingarten_frame_of_pairings {A B n nx ny : Fin 3 → ℝ} {g b c : ℝ}
    (hg : 0 < g) (hA : A ⬝ᵥ A = g) (hB : B ⬝ᵥ B = g) (hAB : A ⬝ᵥ B = 0)
    (hnn : n ⬝ᵥ n = 1) (hnA : n ⬝ᵥ A = 0) (hnB : n ⬝ᵥ B = 0)
    (hnx : n ⬝ᵥ nx = 0) (hny : n ⬝ᵥ ny = 0)
    (hxa : nx ⬝ᵥ A = -b) (hxb : nx ⬝ᵥ B = -c) (hya : ny ⬝ᵥ A = -c) (hyb : ny ⬝ᵥ B = b) :
    ConformalNormalFrame A B n nx ny g b c := by
  have hba := (dotProduct_comm B A).trans hAB
  have expand (W : Fin 3 → ℝ) (hw : n ⬝ᵥ W = 0) :
      g • W = (W ⬝ᵥ A) • A + (W ⬝ᵥ B) • B := by
    apply sub_eq_zero.mp
    apply conformal_triple_orthogonal_zero hg hA hB hAB hnn hnA hnB <;>
      simp only [dotProduct_sub,dotProduct_add,dotProduct_smul,smul_eq_mul,hA,hB,hAB,hba,hnA,hnB,hw,
        dotProduct_comm A W,dotProduct_comm B W] <;> ring
  have ex := expand nx hnx
  have ey := expand ny hny
  rw [hxa,hxb] at ex
  rw [hya,hyb] at ey
  have hxx := congrArg (fun U => nx ⬝ᵥ U) ex
  have hyy := congrArg (fun U => ny ⬝ᵥ U) ey
  have hxy := congrArg (fun U => nx ⬝ᵥ U) ey
  simp only [dotProduct_smul,dotProduct_add,smul_eq_mul,hxa,hxb,hya,hyb] at hxx hyy hxy
  refine ⟨hg,hA,hB,hAB,hnn,hnA,hnB,hnx,hny,?_,?_,?_,hxa,hxb,hya,hyb⟩
  · apply (eq_div_iff hg.ne').mpr
    linear_combination hxx
  · apply (eq_div_iff hg.ne').mpr
    linear_combination hyy
  · exact (mul_eq_zero.mp (show g*(nx ⬝ᵥ ny) = 0 by linear_combination hxy)).resolve_left hg.ne'

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weingarten_frame_of_pairings
