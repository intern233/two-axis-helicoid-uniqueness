import TwoAxisHelicoid.HolomorphicCoverPullback
import TwoAxisHelicoid.MarkedPuncturedUniformization

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold OnePoint

/-- A biholomorphic identification with the punctured model gives a
pointed biholomorphic compactification, on the original one-point
compactification and with holomorphic original inclusion. -/
theorem punctured_biholomorphic_identification_fills {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {L : PeriodPair} (U : M ≃ₜ PuncturedPeriodTorus L) (hU : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U) :
    ∃ S : ChartedSpace ℂ (OnePoint M), let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
      ∃ H : OnePoint M ≃ₜ PeriodTorus L, H OnePoint.infty = 0 ∧
        ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
        ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M) ∧
        ∀ x : M, H (x : OnePoint M) = (U x).1 := by
  let H := U.onePointCongr.trans (punctureCompactification (0:PeriodTorus L))
  have hlocal : IsLocalHomeomorph H := H.isOpenEmbedding.isLocalHomeomorph
  let S := holomorphicCoverAtlas hlocal
  refine ⟨S,?_⟩
  let := S
  have hm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := holomorphicCoverAtlas_isManifold hlocal
  have h := holomorphicCoverAtlas_localDiffeomorph hlocal
  let D := h.diffeomorphOfBijective H.bijective
  have hD (x : OnePoint M) : D x = H x := rfl
  have hi : (D.symm : PeriodTorus L → OnePoint M) = H.symm := by
    funext q
    apply H.injective
    exact (hD _).symm.trans ((D.apply_symm_apply q).trans (H.apply_symm_apply q).symm)
  have hh : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm := hi ▸ D.symm.contMDiff
  have he (x : M) : H (x : OnePoint M) = (U x).1 := rfl
  refine ⟨hm,H,rfl,h.contMDiff,hh,?_,he⟩
  have hc := hh.comp ((contMDiff_subtype_val (U := puncturedPeriodTorusOpen L)).comp hU)
  apply hc.congr
  intro x
  exact ((congrArg H.symm (he x).symm).trans (H.symm_apply_apply _)).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_biholomorphic_identification_fills
