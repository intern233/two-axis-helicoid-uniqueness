import TwoAxisHelicoid.SmoothMarkingFromPhysicalTorus
import TwoAxisHelicoid.UnmarkedHelicoidGraphDifferential
import TwoAxisHelicoid.UnmarkedHelicoidSpinCompactification
import TwoAxisHelicoid.MinimalHelicoidHeightGraphUpgrade

namespace TwoAxisHelicoid
open Complex Set Function Topology InnerProductSpace
open scoped Topology ContDiff Manifold
universe u v

/-- A surface with topologically one handle and no axis marking acquires a
harmonic torus parametrization from its real minimal immersion and the
decay of the height of a single helicoidal graph. -/
theorem harmonic_model_of_topological_handle_height_end {M : Type v} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (minimal : ∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0)
    (height : HasHelicoidHeightEnd (coordinateToTube ∘ X)) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ),
      (∀ x, Y (f x).1=X x) ∧ ∀ z∉L.lattice,
        (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
        Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z) := by
  have tail := punctured_handle_connected_tails top
  have graph := minimal_helicoid_height_graph_is_C1 X cl (smooth_surface_regular_manifold_chart sm imm) minimal tail height
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus L₀)
  let _ : NoncompactSpace M := ⟨fun h => noncompact_univ (PuncturedPeriodTorus L₀) (by
    simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  have op : IsOpen {q : PeriodTorus L₀ | q≠0} := isOpen_compl_singleton
  have refData : IsLocalHomeomorph (fun x => (top x).1) :=
    (op.isOpenEmbedding_subtypeVal.comp top.isOpenEmbedding).isLocalHomeomorph
  obtain ⟨S,man,charts⟩ := minimal_harmonic_atlas_of_topological_reference refData sm imm minimal
  let _ := S
  let _ := man
  have harm := fun e he => (charts e he).2
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling cl harm graph topological_plane_uniformization_proved
  obtain ⟨L,f,Y,_,_,pos,_,_,reg⟩ := marked_harmonic_torus_of_filling top
    (compact_genus_one_uniformization_of_annular_classification annular_riemann_surface_uniformization_proved _)
    X cl harm E hol
  exact ⟨L,f,Y,pos,fun z hz => ⟨(reg z hz).1,(reg z hz).2.2⟩⟩

/-- Proposition 4.4 for an actual minimal surface of topological genus
one. The smooth marking for the original immersion, the cap and the spin
extension are constructed. A smoothing theorem for abstract surfaces is
unnecessary for this case. -/
theorem topological_minimal_handle_height_end_even {M : Type v} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (minimal : ∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0)
    (height : HasHelicoidHeightEnd (coordinateToTube ∘ X)) :
    ∃ (L : PeriodPair) (e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞),
      EvenSpinExtensionInMarking.{u} X e := by
  obtain ⟨L,f,Y,agrees,regular⟩ := harmonic_model_of_topological_handle_height_end top X cl sm imm minimal height
  obtain ⟨e,_⟩ := smooth_marking_of_harmonic_torus_model f Y sm imm agrees regular
  have inv : ContDiff ℝ ∞ coordinateTubeHomeomorph.symm := by
    change ContDiff ℝ ∞ tubeCartesian
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp [tubeCartesian] <;> fun_prop
  exact ⟨L,e,abstract_helicoidal_surface_even_in_smooth_marking X cl sm imm coordinateTubeHomeomorph
    coordinateToTube.contDiff inv height e⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.topological_minimal_handle_height_end_even

