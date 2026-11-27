import TwoAxisHelicoid.ConformalJacobiFrame
import TwoAxisHelicoid.HarmonicChartUnitNormal
import TwoAxisHelicoid.SimilaritySymmetry
import TwoAxisHelicoid.ConformalPlaneColumns

namespace TwoAxisHelicoid
open Complex Matrix

/-- Vanishing normal component gives an actual preimage of the ambient
similarity velocity under the regular chart derivative. -/
theorem similarity_normal_zero_is_tangent {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : AnalyticAt ℝ X z) (hc : ConformalCoordinateDerivatives X z)
    (hi : Function.Injective (fderiv ℝ X z)) (a b : Fin 3 → ℝ) (d : ℝ)
    (h : similarityNormal X (harmonicChartNormal X) a b d z = 0) :
    ∃ w : ℂ, fderiv ℝ X z w = similarityField a b d (X z) := by
  let D := fderiv ℝ X z
  let A := D 1
  let B := D I
  let n := harmonicChartNormal X z
  let g := A ⬝ᵥ A
  let V := similarityField a b d (X z)
  obtain ⟨_,hg,hbb,hab,_,hnn,hna,hnb⟩ := harmonicChartNormal_data hX hc hi
  have hg' : g ≠ 0 := hg.ne'
  have hb : B ⬝ᵥ B = g := hbb.symm
  have ho : A ⬝ᵥ B = 0 := hab
  change n ⬝ᵥ A = 0 at hna
  change n ⬝ᵥ B = 0 at hnb
  have hn : n ⬝ᵥ V = 0 := (dotProduct_comm _ _).trans h
  let w : ℂ := ⟨(A ⬝ᵥ V)/g,(B ⬝ᵥ V)/g⟩
  have hvec := real_complex_map_columns D w
  change D w = ((A ⬝ᵥ V)/g) • A+((B ⬝ᵥ V)/g) • B at hvec
  refine ⟨w,sub_eq_zero.mp ?_⟩
  apply conformal_triple_orthogonal_zero (A := A) (B := B) (n := n) (g := g) hg rfl hb ho hnn hna hnb
  · change A ⬝ᵥ (D w-V) = 0
    rw [hvec,dotProduct_sub,dotProduct_add,dotProduct_smul,dotProduct_smul,ho]
    change ((A ⬝ᵥ V)/g)*g+((B ⬝ᵥ V)/g)*0-(A ⬝ᵥ V) = 0
    simp [hg']
  · change B ⬝ᵥ (D w-V) = 0
    rw [hvec,dotProduct_sub,dotProduct_add,dotProduct_smul,dotProduct_smul,(dotProduct_comm B A).trans ho,hb]
    simp [smul_eq_mul,hg']
  · change n ⬝ᵥ (D w-V) = 0
    rw [hvec,dotProduct_sub,dotProduct_add,dotProduct_smul,dotProduct_smul,hna,hnb,hn]
    simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.similarity_normal_zero_is_tangent
