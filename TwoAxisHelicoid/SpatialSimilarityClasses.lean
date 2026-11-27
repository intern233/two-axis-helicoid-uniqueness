import TwoAxisHelicoid.EuclideanDilationIsometry

namespace TwoAxisHelicoid
open Set

/-- Equivalence of geometric images under all bijective positive-ratio
metric similarities. -/
def spatialSimilaritySetoid (E : Type*) [PseudoMetricSpace E] : Setoid (Set E) where
  r s t := ∃ f : E ≃ᵈ E, f '' s = t
  iseqv := {
    refl := by intro s; exact ⟨DilationEquiv.refl _,image_id s⟩
    symm := by
      rintro s _ ⟨f,rfl⟩
      refine ⟨f.symm,?_⟩
      ext v
      simp
    trans := by
      rintro s _ _ ⟨f,rfl⟩ ⟨g,rfl⟩
      refine ⟨f.trans g,?_⟩
      exact (image_image (g : E → E) (f : E → E) s).symm }

/-- The quotient relation is precisely the original geometric equivalence
by a Euclidean isometry and positive spatial scale. -/
theorem spatial_similarity_iff_positive_scale_isometry {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S T : Set E) : (spatialSimilaritySetoid E).r S T ↔
    ∃ (k : ℝ) (f : E ≃ᵢ E), 0 < k ∧ (fun u => k • f u) '' S = T := by
  constructor
  · rintro ⟨f,rfl⟩
    obtain ⟨k,U,hk,h⟩ := dilation_eq_positive_smul_isometry f
    exact ⟨k,U,hk,congrArg (fun g : E → E => g '' S) (funext h).symm⟩
  · rintro ⟨k,U,hk,rfl⟩
    refine ⟨U.toDilationEquiv.trans (DilationEquiv.smulTorsor (0:E) hk.ne'),?_⟩
    exact congrArg (fun g : E → E => g '' S) (funext fun u => (add_zero (k • U u)))

/-- A surjective change of parameters and pointwise spatial similarity
place the two geometric images in the same class. -/
theorem image_similarity_of_surjective_parameters {P Q E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : P → E) (Y : Q → E) (u : P → Q) (hu : Function.Surjective u)
    (k : ℝ) (e : E ≃ᵢ E) (b : E) (hk : 0 < k) (h : ∀ p, Y (u p) = k • e (X p)+b) :
    (spatialSimilaritySetoid E).r (range X) (range Y) := by
  refine ⟨e.toDilationEquiv.trans (DilationEquiv.smulTorsor b hk.ne'),?_⟩
  ext v
  constructor
  · rintro ⟨_,⟨p,rfl⟩,rfl⟩
    exact ⟨u p,h p⟩
  · rintro ⟨q,rfl⟩
    obtain ⟨p,rfl⟩ := hu q
    exact ⟨_,⟨p,rfl⟩,(h p).symm⟩

/-- Existence of a representative combined with comparison to a single
geometric model gives existence and uniqueness in the similarity quotient. -/
theorem unique_spatial_image_class_of_common_model {A E : Type*} [PseudoMetricSpace E]
    (X : A → Set E) (M : Set E) (hex : Nonempty A) (h : ∀ a, (spatialSimilaritySetoid E).r (X a) M) :
    ∃! c : Quotient (spatialSimilaritySetoid E), ∃ a : A, Quotient.mk (spatialSimilaritySetoid E) (X a) = c := by
  obtain ⟨a⟩ := hex
  refine ⟨Quotient.mk (spatialSimilaritySetoid E) M,⟨a,Quotient.sound (h a)⟩,?_⟩
  rintro c ⟨b,rfl⟩
  exact Quotient.sound (h b)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_similarity_iff_positive_scale_isometry
#print axioms TwoAxisHelicoid.unique_spatial_image_class_of_common_model
