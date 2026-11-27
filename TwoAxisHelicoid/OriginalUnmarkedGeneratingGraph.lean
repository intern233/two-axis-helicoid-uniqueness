import TwoAxisHelicoid.UnmarkedGenusOneCoreGraph
import TwoAxisHelicoid.RegularOriginalSurfaceNormals

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- Local convergence of the actual surfaces and their unoriented unit
normals gives exactly one continuous normal graph on the full two-loop
core. All reference and moving charts are obtained from the original
smooth minimal representatives. The displacements tend to zero
uniformly, including on approach to the boundary of the open core. -/
theorem original_unmarked_normals_give_single_generating_core_graph (s : OriginalSmoothHelicoid)
    (C : TorusGeneratingCoreModel s.modelTorus) (moving : ℕ → OriginalSmoothHelicoid)
    (conv : LocalSpatialImageLimit (fun n => (moving n).unorientedNormals) s.unorientedNormals) :
    let V := {b : s.carrier | (s.topologicalType b).1∈C.carrier}
    ∃ (N : s.carrier → SurfaceEuclideanSpace) (R : ℝ), Continuous N ∧ (∀ b, ‖N b‖=1) ∧ 0<R ∧
      let TV := fun q : V × ℝ => s.euclideanPosition q.1.1+q.2 • N q.1.1
      (∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ q∈spatialTubeSlice TV (range (moving n).euclideanPosition) R, |q.2|<ε) ∧
      ∀ᶠ n in atTop, IsHomeomorph (fun q : spatialTubeSlice TV (range (moving n).euclideanPosition) R => q.1.1) ∧
        ∃ h : V → ℝ, Continuous h ∧ (∀ b, |h b|<R) ∧
          spatialTubeSlice TV (range (moving n).euclideanPosition) R=range (fun b => (b,h b)) := by
  let _ := periodTorus_compactSpace s.modelTorus
  let m := (Subtype.val : PuncturedPeriodTorus s.modelTorus → PeriodTorus s.modelTorus) ∘ s.topologicalType
  let V := m ⁻¹' C.carrier
  let K := m ⁻¹' closure C.carrier
  have en : IsEmbedding m := IsEmbedding.subtypeVal.comp s.topologicalType.isEmbedding
  have vo : IsOpen V := C.isOpen_carrier.preimage en.continuous
  have kc : IsCompact K := by
    apply en.isCompact_iff.mpr
    rw [image_preimage_eq_of_subset]
    · exact isClosed_closure.isCompact
    · intro q hq
      have nz : q≠0 := fun eq => C.closure_avoids (eq ▸ hq)
      exact ⟨s.topologicalType.symm ⟨q,nz⟩,congrArg Subtype.val (s.topologicalType.apply_symm_apply _)⟩
  have sub : closure V⊆K := closure_minimal (fun _ h => subset_closure h) (isClosed_closure.preimage en.continuous)
  let i := fun b : V => (⟨m b.1,b.2⟩ : C.carrier)
  have ie : IsEmbedding i := (en.comp IsEmbedding.subtypeVal).codRestrict C.carrier (fun b => b.2)
  have onto : Function.Surjective i := by
    intro q
    have nz : q.1≠0 := fun eq => C.closure_avoids (eq ▸ subset_closure q.2)
    let b := s.topologicalType.symm ⟨q.1,nz⟩
    have atb : m b=q.1 := congrArg Subtype.val (s.topologicalType.apply_symm_apply _)
    exact ⟨⟨b,by change m b∈C.carrier; rw [atb]; exact q.2⟩,Subtype.ext atb⟩
  let h := ie.toHomeomorphOfSurjective onto
  have compactV := kc.of_isClosed_subset isClosed_closure sub
  have embedded (t : OriginalSmoothHelicoid) : IsClosedEmbedding t.euclideanPosition :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp t.closedEmbedding
  obtain ⟨N,cn,unit,ns,S,data⟩ := original_smooth_regular_normal_geometry s
  choose field _ units norms charts regular using (fun n => original_smooth_regular_normal_geometry (moving n))
  let _ := S
  obtain ⟨U,r,uo,ku,rp,tube⟩ := compact_immersed_core_normal_tube compactV (embedded s).injective.injOn (fun b _ => data b)
  have convergence : LocalSpatialImageLimit (fun n => unorientedSurfaceNormals (moving n).euclideanPosition (field n))
      (unorientedSurfaceNormals s.euclideanPosition N) := by simpa only [norms,ns] using conv
  obtain ⟨R,positive,_,thin,graph⟩ := unmarked_embedded_handles_form_one_core_graph C (embedded s) cn vo h compactV
    (fun b _ => ⟨S.chartAt b,S.mem_chart_source b,data b⟩) uo ku rp tube (fun n => (moving n).topologicalType)
    (fun n => (moving n).euclideanPosition) field (fun n => embedded (moving n)) units
    (fun n b => ⟨(charts n).chartAt b,(charts n).mem_chart_source b,(regular n b).1,(regular n b).2.2.1,(regular n b).2.2.2.2⟩) convergence
  exact ⟨N,R,cn,unit,positive,thin,graph⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_unmarked_normals_give_single_generating_core_graph
