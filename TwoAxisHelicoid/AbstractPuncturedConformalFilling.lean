import TwoAxisHelicoid.HolomorphicCoverPullback
import TwoAxisHelicoid.CompactPunctureHomeomorphism

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology Manifold ContDiff OnePoint

/-- Pass from any compact Riemann surface punctured at one point to the
canonical one-point compactification of the given surface. The original
conformal identification is preserved on every finite point. -/
theorem abstract_punctured_conformal_filling {M N : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [TopologicalSpace N] [T2Space N] [CompactSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ,ℂ) ω N]
    (p : N) (j : M ≃ₜ {q : N // q ≠ p})
    (hj : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x => (j x).1)) :
    ∃ S : ChartedSpace ℂ (OnePoint M), let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
      ∃ D : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) (OnePoint M) N ω, (∀ x : M, D (x:OnePoint M) = (j x).1) ∧
        D ∞ = p ∧ IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M) := by
  let H := j.onePointCongr.trans (punctureCompactification p)
  let S := holomorphicCoverAtlas H.isLocalHomeomorph
  let _ := S
  have hm : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := holomorphicCoverAtlas_isManifold H.isLocalHomeomorph
  have hd := holomorphicCoverAtlas_localDiffeomorph H.isLocalHomeomorph
  let D := hd.diffeomorphOfBijective H.bijective
  have hDx (x : M) : D (x : OnePoint M) = (j x).1 := rfl
  have he : (OnePoint.some : M → OnePoint M) = D.symm ∘ (fun x => (j x).1) := by
    funext x
    exact (D.toHomeomorph.symm_apply_eq.mpr (hDx x).symm).symm
  refine ⟨S,hm,D,hDx,rfl,?_⟩
  rw [he]
  exact fun x => IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := OnePoint M) (hj x) (D.symm.isLocalDiffeomorph _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.abstract_punctured_conformal_filling
