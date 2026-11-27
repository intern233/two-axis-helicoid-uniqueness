import TwoAxisHelicoid.MinimalHeightEndSpinMarking

namespace TwoAxisHelicoid
open Complex Matrix Set Function Topology
open scoped ContDiff Manifold Matrix
universe u v

/-- On a topologically one-handled minimal surface a single helicoidal
height graph in an arbitrary Euclidean similarity frame supplies a
smooth marking and a unique even spin extension of the physical
immersion. The cap agrees with its untransformed position on a core. -/
theorem placed_minimal_handle_height_end_even {M : Type v} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (minimal : ∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0)
    (A : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)) (d : Fin 3 → ℝ) {k : ℝ}
    (metric : ∀ v w, A v ⬝ᵥ A w=k*(v ⬝ᵥ w))
    (height : HasHelicoidHeightEnd (fun x => coordinateToTube (d+A (X x)))) :
    ∃ (L : PeriodPair) (e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞),
      EvenSpinExtensionInMarking.{u} X e := by
  let B := A.toHomeomorph.trans (Homeomorph.addLeft d)
  let Y := B ∘ X
  have regB : ContMDiff 𝓘(ℝ,Fin 3 → ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ B :=
    contMDiff_const.add A.toContinuousLinearMap.contMDiff
  have smoothY : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ Y := regB.comp sm
  have dB (v : Fin 3 → ℝ) : fderiv ℝ B v=A.toContinuousLinearMap := by
    change fderiv ℝ (fun w => d+A w) v=_
    rw [fderiv_const_add]
    exact A.toContinuousLinearMap.hasFDerivAt.fderiv
  have injY (x : M) : Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) Y x) := by
    change Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (B ∘ X) x)
    rw [mfderiv_comp x (regB.mdifferentiable (by simp) _) (sm.mdifferentiable (by simp) _),
      mfderiv_eq_fderiv,dB]
    exact A.injective.comp (imm x)
  have minY (x : M) : coordinateMeanCurvature (Y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0 := by
    have linear := coordinate_minimal_linear_similarity A metric (minimal x)
    exact coordinate_minimal_orthogonal_affine (ContinuousLinearEquiv.refl ℝ _) (fun _ _ => rfl) d linear
  obtain ⟨L,f,Z,eqn,reg⟩ := harmonic_model_of_topological_handle_height_end top Y
    (B.isClosedEmbedding.comp cl) smoothY injY minY height
  obtain ⟨e,_⟩ := smooth_marking_of_harmonic_torus_model f Z smoothY injY eqn reg
  have sB : ContDiff ℝ ∞ B := contDiff_const.add A.contDiff
  have siB : ContDiff ℝ ∞ B.symm := A.symm.contDiff.comp (contDiff_const.add contDiff_id)
  have tubeInv : ContDiff ℝ ∞ coordinateTubeHomeomorph.symm := by
    change ContDiff ℝ ∞ tubeCartesian
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp [tubeCartesian] <;> fun_prop
  exact ⟨L,e,abstract_helicoidal_surface_even_in_smooth_marking X cl sm imm
    (B.trans coordinateTubeHomeomorph) (coordinateToTube.contDiff.comp sB) (siB.comp tubeInv) height e⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.placed_minimal_handle_height_end_even

