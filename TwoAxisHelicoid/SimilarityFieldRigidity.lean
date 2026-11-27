import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

namespace TwoAxisHelicoid
open Matrix

noncomputable def similarityField (a b : Fin 3 → ℝ) (d : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  a+b ⨯₃ x+d • x

theorem cross_annihilates_independent_pair {b u v : Fin 3 → ℝ}
    (huv : LinearIndependent ℝ ![u,v]) (hu : b ⨯₃ u = 0) (hv : b ⨯₃ v = 0) : b = 0 := by
  by_contra hb
  have hbu : ¬LinearIndependent ℝ ![b,u] := by
    intro h
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr h) hu
  have hbv : ¬LinearIndependent ℝ ![b,v] := by
    intro h
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr h) hv
  rw [LinearIndependent.pair_iff' hb] at hbu hbv
  obtain ⟨r,hr⟩ := not_forall.mp hbu
  obtain ⟨s,hs⟩ := not_forall.mp hbv
  have hr' : r • b = u := not_not.mp hr
  have hs' : s • b = v := not_not.mp hs
  apply (crossProduct_ne_zero_iff_linearIndependent.mpr huv)
  simp [← hr',← hs']

theorem similarity_linear_part_annihilates_pair {b u v : Fin 3 → ℝ} {d : ℝ}
    (huv : LinearIndependent ℝ ![u,v])
    (hu : b ⨯₃ u+d • u = 0) (hv : b ⨯₃ v+d • v = 0) : b = 0 ∧ d = 0 := by
  have hun : u ≠ 0 := by simpa using huv.ne_zero 0
  have hd : d = 0 := by
    have h := congrArg (fun w => u ⬝ᵥ w) hu
    simp only [dotProduct_add,dot_cross_self,dotProduct_smul,zero_add,dotProduct_zero,
      smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (fun he => hun (dotProduct_self_eq_zero.mp he))
  rw [hd,zero_smul,add_zero] at hu hv
  exact ⟨cross_annihilates_independent_pair huv hu hv,hd⟩

/-- A similarity infinitesimal field cannot vanish on three noncollinear
points unless all seven translation, rotation and dilation coefficients vanish. -/
theorem similarityField_zero_on_noncollinear_triple {a b p q r : Fin 3 → ℝ} {d : ℝ}
    (hpq : LinearIndependent ℝ ![q-p,r-p])
    (hp : similarityField a b d p = 0)
    (hq : similarityField a b d q = 0)
    (hr : similarityField a b d r = 0) : a = 0 ∧ b = 0 ∧ d = 0 := by
  have hu : b ⨯₃ (q-p)+d • (q-p) = 0 := by
    rw [map_sub,smul_sub]
    have h := congrArg₂ (fun x y : Fin 3 → ℝ => x-y) hq hp
    dsimp [similarityField] at h
    simpa only [sub_self] using (show b ⨯₃ q-b ⨯₃ p+(d • q-d • p) = 0 by
      linear_combination h)
  have hv : b ⨯₃ (r-p)+d • (r-p) = 0 := by
    rw [map_sub,smul_sub]
    have h := congrArg₂ (fun x y : Fin 3 → ℝ => x-y) hr hp
    dsimp [similarityField] at h
    simpa only [sub_self] using (show b ⨯₃ r-b ⨯₃ p+(d • r-d • p) = 0 by
      linear_combination h)
  obtain ⟨hb,hd⟩ := similarity_linear_part_annihilates_pair hpq hu hv
  refine ⟨?_,hb,hd⟩
  simpa [similarityField,hb,hd] using hp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.similarityField_zero_on_noncollinear_triple
