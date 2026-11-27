import TwoAxisHelicoid.HolomorphicNullImmersion
import Mathlib.LinearAlgebra.CrossProduct

namespace TwoAxisHelicoid
open Complex Matrix InnerProductSpace Laplacian
open scoped Topology

/-- The Euclidean unit normal obtained from the oriented tangent cross
product. Euclidean dot products are used explicitly, not the sup norm. -/
noncomputable def unitCrossNormal (A B : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (Real.sqrt ((A ⨯₃ B) ⬝ᵥ (A ⨯₃ B)))⁻¹ • (A ⨯₃ B)

theorem conformal_unitCrossNormal {A B : Fin 3 → ℝ} {g : ℝ}
    (hg : 0 < g) (hA : A ⬝ᵥ A = g) (hB : B ⬝ᵥ B = g) (hAB : A ⬝ᵥ B = 0) :
    unitCrossNormal A B ⬝ᵥ unitCrossNormal A B = 1 ∧
      unitCrossNormal A B ⬝ᵥ A = 0 ∧ unitCrossNormal A B ⬝ᵥ B = 0 := by
  have hcross : (A ⨯₃ B) ⬝ᵥ (A ⨯₃ B) = g^2 := by
    rw [cross_dot_cross,hA,hB,hAB,zero_mul,sub_zero,pow_two]
  have hNA : (A ⨯₃ B) ⬝ᵥ A = 0 := (dotProduct_comm _ _).trans (dot_self_cross A B)
  have hNB : (A ⨯₃ B) ⬝ᵥ B = 0 := (dotProduct_comm _ _).trans (dot_cross_self A B)
  simp only [unitCrossNormal,smul_dotProduct,dotProduct_smul,smul_eq_mul,hcross,
    Real.sqrt_sq hg.le,hNA,hNB,mul_zero,and_self]
  field_simp
  exact ⟨trivial,trivial⟩

/-- The standard scalar mean-curvature formula from the first and second
fundamental forms in a complex parameter. The normal and every derivative
are computed from the actual map. -/
noncomputable def coordinateMeanCurvature (X : ℂ → Fin 3 → ℝ) (z : ℂ) : ℝ :=
  let A := fderiv ℝ X z 1
  let B := fderiv ℝ X z I
  let N := unitCrossNormal A B
  ((B ⬝ᵥ B)*(iteratedFDeriv ℝ 2 X z ![1,1] ⬝ᵥ N)-
    2*(A ⬝ᵥ B)*(iteratedFDeriv ℝ 2 X z ![1,I] ⬝ᵥ N)+
    (A ⬝ᵥ A)*(iteratedFDeriv ℝ 2 X z ![I,I] ⬝ᵥ N)) /
      (2*((A ⬝ᵥ A)*(B ⬝ᵥ B)-(A ⬝ᵥ B)^2))

/-- Harmonicity and conformality force the actual mean curvature to
vanish. This identifies the standard geometric formula, rather than
using the word minimal as a synonym in a definition. -/
theorem conformal_harmonic_coordinate_mean_curvature_zero
    {X : ℂ → Fin 3 → ℝ} {z : ℂ} {g : ℝ}
    (hX : HarmonicAt X z)
    (hA : fderiv ℝ X z 1 ⬝ᵥ fderiv ℝ X z 1 = g)
    (hB : fderiv ℝ X z I ⬝ᵥ fderiv ℝ X z I = g)
    (hAB : fderiv ℝ X z 1 ⬝ᵥ fderiv ℝ X z I = 0) :
    coordinateMeanCurvature X z = 0 := by
  have hLap : iteratedFDeriv ℝ 2 X z ![1,1]+iteratedFDeriv ℝ 2 X z ![I,I] = 0 := by
    have h := hX.2.self_of_nhds
    simpa only [laplacian_eq_iteratedFDeriv_complexPlane,Pi.zero_apply] using h
  unfold coordinateMeanCurvature
  dsimp only
  rw [hA,hB,hAB]
  simp only [mul_zero,zero_mul,sub_zero]
  rw [← mul_add,← add_dotProduct,hLap,zero_dotProduct,mul_zero,zero_div]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conformal_harmonic_coordinate_mean_curvature_zero
