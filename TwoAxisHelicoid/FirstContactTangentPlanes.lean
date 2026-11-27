import TwoAxisHelicoid.TransverseDoublePointPersistence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace TwoAxisHelicoid
open Set Filter Topology Module
open scoped Topology ContDiff

/-- Two different tangent hyperplanes span the ambient space. Written as
a difference of velocities, this is exactly the differential of the
two-sheet position difference. -/
theorem difference_surjective_of_distinct_tangent_planes {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A B : E →L[ℝ] V) (ha : Function.Injective A) (hb : Function.Injective B)
    (hd : finrank ℝ V = finrank ℝ E+1) (hne : A.range ≠ B.range) :
    ∀ y : V, ∃ u v : E, A u - B v = y := by
  have hA : finrank ℝ A.range = finrank ℝ E := LinearMap.finrank_range_of_inj ha
  have hB : finrank ℝ B.range = finrank ℝ E := LinearMap.finrank_range_of_inj hb
  have hlt : A.range < A.range ⊔ B.range := by
    refine lt_of_le_of_ne le_sup_left fun he => hne ?_
    exact (Submodule.eq_of_le_of_finrank_le (show B.range ≤ A.range from he ▸ le_sup_right) (by omega)).symm
  have hall : A.range ⊔ B.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    have t := (A.range ⊔ B.range).finrank_le
    omega
  intro y
  have hym : y ∈ A.range ⊔ B.range := hall ▸ Submodule.mem_top
  obtain ⟨_,⟨u,rfl⟩,_,⟨v,rfl⟩,eq⟩ := Submodule.mem_sup.mp hym
  exact ⟨u,-v,by simpa using eq⟩

/-- At first loss of injectivity a coincident pair of regular hypersurface
sheets has equal tangent spaces. It suffices that points on the two
patches never coincide for a cofinal set of nearby parameters. -/
theorem tangent_planes_agree_at_limit_contact {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (F : ℝ × E → V) {t : ℝ} {a b : E} (hab : a ≠ b) (he : F (t,a) = F (t,b))
    (ha : ContDiffAt ℝ 1 F (t,a)) (hb : ContDiffAt ℝ 1 F (t,b))
    (hi : Function.Injective (fderiv ℝ (fun z => F (t,z)) a))
    (hj : Function.Injective (fderiv ℝ (fun z => F (t,z)) b))
    (hd : finrank ℝ V = finrank ℝ E+1)
    {U W : Set E} (hU : U ∈ 𝓝 a) (hW : W ∈ 𝓝 b)
    (hsep : ∃ᶠ s in 𝓝 t, ∀ u ∈ U, ∀ v ∈ W, u ≠ v → F (s,u) ≠ F (s,v)) :
    (fderiv ℝ (fun z => F (t,z)) a).range = (fderiv ℝ (fun z => F (t,z)) b).range := by
  by_contra hn
  have pers := transverse_double_point_persists F t hab he ha hb
    (difference_surjective_of_distinct_tangent_planes _ _ hi hj hd hn) hU hW
  obtain ⟨s,sep,u,hu,v,hv,hne,eq⟩ := (hsep.and_eventually pers).exists
  exact sep u hu v hv hne eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.tangent_planes_agree_at_limit_contact
