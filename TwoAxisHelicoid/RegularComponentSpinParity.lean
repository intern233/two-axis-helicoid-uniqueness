import TwoAxisHelicoid.EssentialLevelCirclePeriod
import TwoAxisHelicoid.RegularTorusLevelParametrization
import TwoAxisHelicoid.RegularPlaneCutSpinParity

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- A regular horizontal level component on which the two marked phase
coordinates have no simultaneous real angles forces the ambient spin
of the embedded torus to be even. Both its plane traversal and its
nonzero lattice period are derived from the actual level component. -/
theorem embedded_torus_even_of_nonlifting_regular_height (L : PeriodPair)
    (F : PeriodTorus L → Fin 3 → ℝ) (continuousF : Continuous F) (embed : Function.Injective F)
    (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (H : PeriodTorus L ≃ₜ Circle × Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    {v : ℝ} (distinct : v≠F 0 2)
    (reg : ∀ z, F (periodTorusProjection L z) 2=v →
      ∃ w, fderiv ℝ (F ∘ periodTorusProjection L) z w 2≠0)
    (x : (fun q => F q 2) ⁻¹' {v})
    (obstruct : ¬∃ a b : ContinuousMap (connectedComponent x) ℝ, ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2) :
    capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)=0 := by
  let π := periodTorusProjection L
  let h := fun q => F q 2
  let P := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 2
  have lift (z : ℂ) (away : h (π z)≠h 0) := spatial_torus_lift_regular_at L F
    (fun hz => away (congrArg h ((periodTorusProjection_eq_zero L z).mpr hz))) sm imm
  obtain ⟨e,ξ,smooth,velocity,projects⟩ := regular_torus_level_component_parametrization L
    (H:=h) (P.continuous.comp continuousF) distinct
    (fun z hz => P.contDiff.contDiffAt.comp z (lift z hz).1) (fun z hz => by
      obtain ⟨w,hw⟩ := reg z hz
      have df := P.hasFDerivAt.comp z ((lift z (fun eq => distinct (hz.symm.trans eq))).1.differentiableAt (by simp)).hasFDerivAt
      exact ⟨w,by change fderiv ℝ (P ∘ (F ∘ π)) z w≠0; rw [df.fderiv]; exact hw⟩) x
  obtain ⟨period,nz,lat,shift⟩ := nonlifting_traversal_displacement L e (fun q => q.1.1)
    H marked obstruct ξ smooth.continuous projects
  have height (t : ℝ) : h (π (ξ t))=v := (congrArg h (projects t)).trans (e (t:OrientationCircle)).1.2
  have off (t : ℝ) : ξ t∉L.lattice := fun mem => distinct ((height t).symm.trans
    (congrArg h ((periodTorusProjection_eq_zero L _).mpr mem)))
  apply embedded_torus_regular_plane_section_even L F embed sm imm smooth off nz lat shift velocity _ height
    (fun t => reg _ (height t))
  intro t d hd same
  rw [projects,projects] at same
  have eq := e.injective (Subtype.ext (Subtype.ext same))
  rw [AddCircle.coe_add] at eq
  have zero : (d : OrientationCircle)=0 := add_eq_left.mp eq
  exact hd.1.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico (Ioo_subset_Ico_self hd)).mp zero)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_torus_even_of_nonlifting_regular_height
