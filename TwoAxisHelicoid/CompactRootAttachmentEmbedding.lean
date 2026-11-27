import TwoAxisHelicoid.CenteredClosedPeriodScaling
import TwoAxisHelicoid.CompactRootAttachmentImmersion
import TwoAxisHelicoid.CompactRootDerivativeFromOriginalRow
import TwoAxisHelicoid.CertifiedGlobalEmbeddingFromCertificates

namespace TwoAxisHelicoid.PdfVertical
open Set Topology

/-- The normalized geometric certificate and any pair of closed periods
in the root attachment's height interval refer to the same point. Here
uniqueness uses only the original derivative row and the root attachment. -/
theorem compact_root_closed_parameters_eq_certified (p : ClosedPeriodParameters)
    (hp : p.t∈Icc (rootTLower:ℝ) rootTUpper) : p=certifiedClosedParameters := by
  let q := certifiedClosedParameters
  have member (r : ClosedPeriodParameters) (hr : r.t∈Icc (rootTLower:ℝ) rootTUpper) :
      (r.t,r.a).1∈Icc (rootTLower:ℝ) rootTUpper ∧ ∃ ht : 0<(r.t,r.a).1,
        (r.t,r.a).2∈Ioo (0:ℝ) 1 ∧ ∀ j : Fin 3,
          (originalCoordinatePeriod r.t r.a 1 ht j).re=0 ∧
          (conjugateCoordinatePeriod r.t r.a 1 ht j).re=0 :=
    ⟨hr,r.height_pos,r.abscissa_mem,
      (original_all_generators_close_iff r.height_pos
        ⟨r.abscissa_mem.1,by linarith [r.abscissa_mem.2]⟩ one_ne_zero).mpr
        ⟨r.vertical_closed,r.horizontal_closed⟩⟩
  obtain ⟨height,_⟩ := certifiedClosedParameters_bounds
  have pair : (p.t,p.a)=(q.t,q.a) :=
    (compact_root_attachment_unique_generators 1 one_ne_zero).unique
      (member p hp) (member q ⟨height.1.le,height.2.le⟩)
  have extPair (u v : ClosedPeriodParameters) (eqn : (u.t,u.a)=(v.t,v.a)) : u=v := by
    obtain ⟨_,_,_,_,_,_⟩ := u
    obtain ⟨_,_,_,_,_,_⟩ := v
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eqn
    rfl
  exact extPair p q pair

/-- The pair supplied directly by the original horizontal endpoint bounds
yields a globally closed embedded centered surface at every nonzero scale.
The spatial injectivity certificate is transferred using the local
uniqueness certified by original derivative row 016. -/
theorem compact_root_attachment_centered_embeddings :
    ∃ p : ClosedPeriodParameters, p.t∈Ioo (rootTLower:ℝ) rootTUpper ∧
      p.a∈Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      ∀ (c : ℝ) (hc : c≠0),
        ClosedImmersionProperties p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed ∧
        IsClosedEmbedding (centeredActualTorusImmersion p.height_pos p.abscissa_mem hc
          p.vertical_closed p.horizontal_closed) := by
  obtain ⟨p,height,abscissa,geom⟩ := compact_root_attachment_reconstructs_immersion
  have identified := compact_root_closed_parameters_eq_certified p ⟨height.1.le,height.2.le⟩
  have unitInj : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair p.t p.height_pos) =>
      actualTorusImmersion p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed q.1) := by
    subst p
    intro x y same
    exact certified_global_closed_embedding.injective (congrArg coordinateToEuclidean same)
  exact ⟨p,height,abscissa,fun c hc => ⟨(geom c hc).2,
    centered_closed_embedding_all_scales p.height_pos p.abscissa_mem hc
      p.vertical_closed p.horizontal_closed unitInj⟩⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compact_root_attachment_centered_embeddings

