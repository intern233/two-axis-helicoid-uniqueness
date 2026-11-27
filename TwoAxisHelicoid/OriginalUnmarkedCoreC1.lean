import TwoAxisHelicoid.OpenCoreChartParameters
import TwoAxisHelicoid.UnmarkedHandleGraphSelection

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A topological marking transfers compactness of the closed core
and the open genus-one marking without differentiating the marking. -/
theorem marked_punctured_handle_core {B : Type*} [TopologicalSpace B] {A : PeriodPair}
    (f : B ≃ₜ PuncturedPeriodTorus A) (C : TorusGeneratingCoreModel A) :
    let V := {b | (f b).1∈C.carrier}
    IsOpen V ∧ IsCompact (closure V) ∧ Nonempty (V ≃ₜ C.carrier) := by
  let _ := periodTorus_compactSpace A
  let m := (Subtype.val : PuncturedPeriodTorus A → PeriodTorus A) ∘ f
  let V := m ⁻¹' C.carrier
  let K := m ⁻¹' closure C.carrier
  have en : IsEmbedding m := IsEmbedding.subtypeVal.comp f.isEmbedding
  have kc : IsCompact K := by
    apply en.isCompact_iff.mpr
    rw [image_preimage_eq_of_subset]
    · exact isClosed_closure.isCompact
    · intro q hq
      have nz : q≠0 := fun eq => C.closure_avoids (eq ▸ hq)
      exact ⟨f.symm ⟨q,nz⟩,congrArg Subtype.val (f.apply_symm_apply _)⟩
  have sub : closure V⊆K := closure_minimal (fun _ h => subset_closure h) (isClosed_closure.preimage en.continuous)
  let i := fun b : V => (⟨m b.1,b.2⟩ : C.carrier)
  have ie : IsEmbedding i := (en.comp IsEmbedding.subtypeVal).codRestrict C.carrier (fun b => b.2)
  have onto : Function.Surjective i := by
    intro q
    have nz : q.1≠0 := fun eq => C.closure_avoids (eq ▸ subset_closure q.2)
    let b := f.symm ⟨q.1,nz⟩
    have atb : m b=q.1 := congrArg Subtype.val (f.apply_symm_apply _)
    exact ⟨⟨b,by change m b∈C.carrier; rw [atb]; exact q.2⟩,Subtype.ext atb⟩
  exact ⟨C.isOpen_carrier.preimage en.continuous,kc.of_isClosed_subset isClosed_closure sub,⟨ie.toHomeomorphOfSurjective onto⟩⟩

/-- Unmarked convergence of the original point--normal sets produces
one open marking on the entire genus-one core of each moving handle.
In all original regular charts these same physical sheets converge C¹,
with uniformly small heights even up to the edge of the core. -/
theorem original_unmarked_handles_converge_C1_on_core (s : OriginalSmoothHelicoid)
    (C : TorusGeneratingCoreModel s.modelTorus) (moving : ℕ → OriginalSmoothHelicoid)
    (conv : LocalSpatialImageLimit (fun n => (moving n).unorientedNormals) s.unorientedNormals) :
    let V := {b : s.carrier | (s.topologicalType b).1∈C.carrier}
    ∃ (N : s.carrier → SurfaceEuclideanSpace) (R : ℝ), Continuous N ∧ (∀ b, ‖N b‖=1) ∧ 0<R ∧
      ∃ (k : ℕ) (b : V) (G : ∀ n, PhysicalCoreGraph (fun q : V × ℝ => s.euclideanPosition q.1.1+q.2 • N q.1.1)
        (moving (n+k)).euclideanPosition R),
        (∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ q, |(G n).height q|<ε) ∧
        ∀ a : OpenPartialHomeomorph s.carrier ℂ, RegularImmersionChart s.position a →
          let U := coreChartRegion V a
          let p := coreChartParameter V b a
          let h := fun n => (G n).height ∘ p
          let Z := fun n => (moving (n+k)).euclideanPosition ∘ (G n).point ∘ p
          (∀ n z, z∈U → ContDiffAt ℝ 1 (h n) z ∧ ContDiffAt ℝ 1 (Z n) z) ∧
            TendstoLocallyUniformlyOn (fun n => fderiv ℝ (h n)) (fun _ => 0) atTop U ∧
            TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ (s.euclideanPosition ∘ a.symm)) atTop U := by
  intro V
  obtain ⟨vo,kc,⟨base⟩⟩ := marked_punctured_handle_core s.topologicalType C
  let b := base.symm C.base
  have embedded (t : OriginalSmoothHelicoid) : IsClosedEmbedding t.euclideanPosition :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp t.closedEmbedding
  obtain ⟨N,cn,unit,ns,S,data⟩ := original_smooth_regular_normal_geometry s
  choose field _ units norms charts regular using (fun n => original_smooth_regular_normal_geometry (moving n))
  have movingChart (n : ℕ) (y : (moving n).carrier) := (regular n y)
  let _ := S
  obtain ⟨U,r,uo,ku,rp,tube⟩ := compact_immersed_core_normal_tube kc (embedded s).injective.injOn (fun y _ => data y)
  have convergence : LocalSpatialImageLimit (fun n => unorientedSurfaceNormals (moving n).euclideanPosition (field n))
      (unorientedSurfaceNormals s.euclideanPosition N) := by simpa only [norms,ns] using conv
  have chart (n : ℕ) (y : (moving n).carrier) : ∃ a : OpenPartialHomeomorph (moving n).carrier ℂ, y∈a.source ∧
      ContDiffAt ℝ 1 ((moving n).euclideanPosition ∘ a.symm) (a y) ∧
      Function.Injective (fderiv ℝ ((moving n).euclideanPosition ∘ a.symm) (a y)) ∧
      ∀ v, ⟪fderiv ℝ ((moving n).euclideanPosition ∘ a.symm) (a y) v,field n y⟫=0 :=
    ⟨(charts n).chartAt y,(charts n).mem_chart_source y,(movingChart n y).1,(movingChart n y).2.2.1,(movingChart n y).2.2.2.2⟩
  obtain ⟨R,pos,_,k,G,angle,limit⟩ := unmarked_handles_select_transverse_core_graphs C (embedded s) cn vo base kc
    (fun y _ => ⟨S.chartAt y,S.mem_chart_source y,data y⟩) uo ku rp tube (fun n => (moving n).topologicalType)
    (fun n => (moving n).euclideanPosition) field (fun n => embedded (moving n)) units chart convergence
  refine ⟨N,R,cn,unit,pos,k,b,G,fun ε ep => (limit ε ep).mono (fun n h q => (h q).1),?_⟩
  intro a reg
  exact physical_graph_C1_on_original_surface s vo b cn unit ns G (fun n => chart (n+k)) (fun n => units (n+k)) angle limit a reg

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_unmarked_handles_converge_C1_on_core
