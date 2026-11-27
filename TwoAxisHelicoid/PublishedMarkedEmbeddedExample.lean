import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem
import TwoAxisHelicoid.MarkedTorusCertifiedRigidity
import TwoAxisHelicoid.CertifiedEmbeddedRepresentative

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology

/-- The existence datum exhibited by Weber--Hoffman--Wolf, Theorem 1 and
§6.3: the crossing is at the origin and the puncture is zero in the marked
torus. Its period pair and its Weierstrass parameters are unspecified. -/
def PublishedMarkedEmbeddedHelicoidExample : Prop :=
  ∃ (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ),
    IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1) ∧
    (∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1)) ∧
    (∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1)) ∧
    (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) ∧
    meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ periodTorusProjection L) w 2)
      0 = (-2 : ℤ) ∧
    meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 = (-2 : ℤ)

/-- The published marked example transfers global embeddedness directly
to the certified period zero, including its central compact part. -/
theorem certified_embedding_of_published_marked_example
    (whw : PublishedMarkedEmbeddedHelicoidExample) : IsClosedEmbedding certifiedTorusImmersion := by
  obtain ⟨L,X,cl,hor,ver,regular,height,gauss⟩ := whw
  obtain ⟨U,k,E,b,hk,h⟩ := marked_straight_axes_similarity_to_certified
    marked_rhombic_helicoid_intersection L X cl hor ver regular height gauss
  let A := E.toDilationEquiv.trans (DilationEquiv.smulTorsor b hk.ne')
  let Xp := fun q : PuncturedPeriodTorus L => X q.1
  have eq : certifiedTorusImmersion = A ∘ coordinateToEuclidean ∘ Xp ∘ U.symm := by
    funext z
    change certifiedTorusImmersion z = k • E (coordinateToEuclidean (X (U.symm z).1)) + b
    simpa only [U.apply_symm_apply] using h (U.symm z)
  rw [eq]
  exact A.toHomeomorph.isClosedEmbedding.comp
    (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding).comp
      (cl.comp U.symm.isClosedEmbedding))

theorem original_c1_representative_of_published_marked_example
    (whw : PublishedMarkedEmbeddedHelicoidExample) : Nonempty OriginalHelicoidRepresentative := by
  obtain ⟨s,_⟩ := certified_original_representative_of_injective
    (certified_embedding_of_published_marked_example whw).injective
  exact ⟨s⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certified_embedding_of_published_marked_example
#print axioms TwoAxisHelicoid.original_c1_representative_of_published_marked_example
