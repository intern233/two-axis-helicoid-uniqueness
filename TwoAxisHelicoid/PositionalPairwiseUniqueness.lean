import TwoAxisHelicoid.IntersectionFreeClassification
import TwoAxisHelicoid.OriginalNormalizedGaussDivisor

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped ContDiff Manifold

/-- Given two original candidates, the positive similarity identifies
their positions point by point under a biholomorphism. The crossing of
the two prescribed axes corresponds under this same map. -/
theorem positional_candidates_pointwise_similar (bbc : PublishedOneHandleEndTheorem)
    (poincare : SimplyConnectedNoncompactUniformization.{0}) (s t : OriginalPositionallyAsymptoticHelicoid) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      ∃ T : ChartedSpace ℂ t.carrier, let _ := T
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ IsManifold 𝓘(ℂ,ℂ) ω t.carrier ∧
      (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
      (∀ d∈atlas ℂ t.carrier, InducedIsothermalChart t.position d) ∧
      ∃ (h : s.carrier ≃ₜ t.carrier) (k : ℝ) (A : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)),
        0<k ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h.symm ∧
        (∀ x, t.euclideanPosition (h x)=k • A (s.euclideanPosition x)) ∧
        ∃ x, s.position x=![0,0,s.axes.horizontalPoint 2] ∧
          t.position (h x)=![0,0,t.axes.horizontalPoint 2] := by
  have model (v : OriginalPositionallyAsymptoticHelicoid) := (published_end_pointed_normalization v bbc
    (compact_genus_one_uniformization_of_classical poincare _) marked_rhombic_helicoid_intersection).2
  obtain ⟨S,hs,cs,U,k,E,b,hu,hi,hk,ps,_,xs,_⟩ := model s
  obtain ⟨T,ht,ct,V,l,J,c,hv,hj,hl,pt,_,xt,_⟩ := model t
  let _ := S
  let _ := T
  let F := E.toDilationEquiv.trans (DilationEquiv.smulTorsor b hk.ne')
  let G := J.toDilationEquiv.trans (DilationEquiv.smulTorsor c hl.ne')
  let D := F.trans G.symm
  let h := U.trans V.symm
  have pos (x : s.carrier) : t.euclideanPosition (h x)=D (s.euclideanPosition x) := by
    change t.euclideanPosition (V.symm (U x))=G.symm (F (s.euclideanPosition x))
    apply G.injective
    rw [G.apply_symm_apply]
    have e : G (t.euclideanPosition (V.symm (U x)))=certifiedTorusImmersion (V (V.symm (U x))) := (pt _).symm
    rw [V.apply_symm_apply] at e
    exact e.trans (ps x)
  obtain ⟨ratio,A,positive,action⟩ := dilation_eq_positive_smul_isometry D
  refine ⟨S,T,hs,ht,cs,ct,h,ratio,A,positive,hj.comp hu,hi.comp hv,fun x => (pos x).trans (action _),_,xs,?_⟩
  let axis : PuncturedPeriodTorus certifiedPeriodPair := rhombicAxisPoint certifiedClosedParameters.height_pos
  exact (congrArg (fun q => t.position (V.symm q)) (U.apply_symm_apply axis)).trans xt

/-- At most one similarity class is represented, independently of
the published existence example. Each representative also has its
simple Gauss divisor in its pointed compact marking. -/
theorem positional_at_most_one_and_pointed_divisor (bbc : PublishedOneHandleEndTheorem)
    (poincare : SimplyConnectedNoncompactUniformization.{0}) :
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Subsingleton ∧
      ∀ s : OriginalPositionallyAsymptoticHelicoid, HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid := by
  constructor
  · rintro _ ⟨s,rfl⟩ _ ⟨t,rfl⟩
    obtain ⟨_,_,_,_,_,_,h,k,A,hk,_,_,pos,_⟩ := positional_candidates_pointwise_similar bbc poincare s t
    exact Quotient.sound (image_similarity_of_surjective_parameters _ _ h h.surjective k A 0 hk
      (fun x => (pos x).trans (add_zero _).symm))
  · intro s
    exact original_pointed_gauss_divisor_of_normalization _ (published_end_pointed_normalization s bbc
      (compact_genus_one_uniformization_of_classical poincare _) marked_rhombic_helicoid_intersection).2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_candidates_pointwise_similar
#print axioms TwoAxisHelicoid.positional_at_most_one_and_pointed_divisor
