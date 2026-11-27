import TwoAxisHelicoid.CyclicAnalyticCoverQuotient
import TwoAxisHelicoid.PuncturedDiskLogCover
import TwoAxisHelicoid.ClassicalRiemannUniformizationSpecialization

namespace TwoAxisHelicoid
open Complex Set Function TopologicalSpace
open scoped Topology ContDiff Manifold

universe u

/-- The simply connected uniformization theorem implies the classical
classification of an abstract annular Riemann surface. Only its
topological annulus marking is supplied. The covering atlas, free
generator and analytic quotient parameter are constructed. -/
theorem annular_uniformization_of_plane_dichotomy {M : Type u} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {R : ℝ} (hR : 0<R)
    (mark : M ≃ₜ {z : ℂ // 0<‖z‖ ∧ ‖z‖<R}) (uni : TopologicalPlaneUniformization.{u}) :
    ∃ T : Opens ℂ, IsRoundCylinderTarget T ∧ Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M T ω) := by
  obtain ⟨p₀,cov,onto,fib⟩ := punctured_disk_cyclic_plane_cover hR
  let Q := ULift.{u} ℂ
  let E : Q ≃ₜ ℂ := Homeomorph.ulift
  let t : ℂ := 2*(Real.pi:ℂ)*I
  have non : t≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  let p := mark.symm ∘ p₀ ∘ E
  have cover : IsCoveringMap p := (cov.comp_homeomorph E).homeomorph_comp mark.symm
  have sur : Surjective p := mark.symm.surjective.comp (onto.comp E.surjective)
  let _ := holomorphicCoverAtlas cover.isLocalHomeomorph
  have man : IsManifold 𝓘(ℂ,ℂ) ω Q := holomorphicCoverAtlas_isManifold cover.isLocalHomeomorph
  have localD := holomorphicCoverAtlas_localDiffeomorph cover.isLocalHomeomorph
  have same {V : Type} [TopologicalSpace V] (Φ : Q ≃ₜ V) (x y : V) :
      (p ∘ Φ.symm) x=(p ∘ Φ.symm) y ↔ ∃ n : ℤ,
        (E.symm.trans Φ).symm x=(E.symm.trans Φ).symm y+(n:ℂ)*t := by
    change mark.symm (p₀ (E (Φ.symm x)))=mark.symm (p₀ (E (Φ.symm y))) ↔ _
    rw [mark.symm.injective.eq_iff]
    exact fib _ _
  rcases uni Q ⟨E⟩ with hp | hd
  · obtain ⟨Φ⟩ := hp
    exact cyclic_holomorphic_plane_quotient non (E.symm.trans Φ.toHomeomorph)
      (cover.comp_homeomorph Φ.symm.toHomeomorph) (sur.comp Φ.symm.surjective)
      (fun z => IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := M) (Φ.symm.isLocalDiffeomorph z) (localD (Φ.symm z)))
      (same Φ.toHomeomorph)
  · obtain ⟨Φ⟩ := hd
    exact cyclic_holomorphic_disk_quotient non (E.symm.trans Φ.toHomeomorph) (sur.comp Φ.symm.surjective)
      (fun z => IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := M) (Φ.symm.isLocalDiffeomorph z) (localD (Φ.symm z)))
      (same Φ.toHomeomorph)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.annular_uniformization_of_plane_dichotomy
