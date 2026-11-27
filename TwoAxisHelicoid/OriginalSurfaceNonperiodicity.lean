import TwoAxisHelicoid.PuncturedTorusNoScrewPeriod
import TwoAxisHelicoid.GeometricHelicoidHypotheses

namespace TwoAxisHelicoid
open Complex Set Topology

/-- An ambient symmetry cannot translate a real coordinate of an embedded
once-punctured torus by a nonzero amount. The topology excludes such periods
for the originally parametrized surface. -/
theorem topological_torus_image_no_drift {M : Type*} [TopologicalSpace M]
    (L : PeriodPair) (top : M ≃ₜ PuncturedPeriodTorus L)
    (X : M → Fin 3 → ℝ) (hX : IsEmbedding X) (s : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (h : (Fin 3 → ℝ) → ℝ) (hc : Continuous h) {d : ℝ} (hd : d ≠ 0)
    (hs : ∀ p, h (s p) = h p+d) : s '' range X ≠ range X := by
  intro he
  let S := range X
  let Y := top.symm.trans hX.toHomeomorph
  let σ := (s.isEmbedding.homeomorphImage S).trans (Homeomorph.setCongr he)
  let E := (Y.trans σ).trans Y.symm
  have eq (q : PuncturedPeriodTorus L) : ((Y (E q)).1 : Fin 3 → ℝ) = s (Y q).1 :=
    congrArg Subtype.val (Y.apply_symm_apply (σ (Y q)))
  apply punctured_torus_no_height_translating_homeomorphism L E (fun q => h (Y q).1)
    (hc.comp (continuous_subtype_val.comp Y.continuous)) hd
  intro q
  rw [eq,hs]

theorem OriginalSmoothHelicoid.no_nonzero_translation (s : OriginalSmoothHelicoid) {v : Fin 3 → ℝ}
    (hv : v ≠ 0) : (fun p => p+v) '' range s.position ≠ range s.position := by
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! ha
    exact hv (funext ha)
  exact topological_torus_image_no_drift s.modelTorus s.topologicalType s.position s.closedEmbedding.isEmbedding
    (Homeomorph.addRight v) (fun p => p j) (continuous_apply j) hj (fun _ => rfl)

theorem OriginalSmoothHelicoid.no_nonzero_screw_step (s : OriginalSmoothHelicoid)
    (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) {d : ℝ} (hd : d ≠ 0) (hR : ∀ p, R p 2 = p 2+d) :
    R '' range s.position ≠ range s.position :=
  topological_torus_image_no_drift s.modelTorus s.topologicalType s.position s.closedEmbedding.isEmbedding
    R (fun p => p 2) (continuous_apply 2) hd hR

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.no_nonzero_translation
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.no_nonzero_screw_step
