import TwoAxisHelicoid.ConvergingCoreTubeCoverage
import TwoAxisHelicoid.OriginalGenusOneCoreTube

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology

/-- On the actual once-punctured surface the two generator loops belong
to a common open core. For any sequence of closed spatial images
converging to the original image, the thinner physical normal tube is
met, has uniformly vanishing height and projects properly. A transverse
sequence therefore covers this entire two-generator core by finitely
many local sheets. -/
theorem original_generating_core_convergent_sheets (s : OriginalSmoothHelicoid) (C : TorusGeneratingCoreModel s.modelTorus)
    (S : ℕ → Set SurfaceEuclideanSpace) (closed : ∀ n, IsClosed (S n))
    (conv : LocalSpatialImageLimit S (range s.euclideanPosition)) :
    let V := {b : s.carrier | (s.topologicalType b).1 ∈ C.carrier}
    ∃ (N : s.carrier → SurfaceEuclideanSpace) (R : ℝ), Continuous N ∧ (∀ b, ‖N b‖=1) ∧ 0<R ∧
      let T := fun q : V × ℝ => s.euclideanPosition q.1.1 + q.2 • N q.1.1
      (∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ q∈spatialTubeSlice T (S n) R, |q.2|<ε) ∧
      ∀ᶠ n in atTop, (spatialTubeSlice T (S n) R).Nonempty ∧
        let p := fun q : spatialTubeSlice T (S n) R => q.1.1
        IsProperMap p ∧ (IsLocalHomeomorph p → Function.Surjective p ∧ ∀ b : V, Nonempty (FiniteSheetGerms p b)) := by
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
  let _ := C.pathConnected
  let _ : PreconnectedSpace V := (h.symm.surjective.connectedSpace h.symm.continuous).toPreconnectedSpace
  have ne : V.Nonempty := ⟨(h.symm C.base).1,(h.symm C.base).2⟩
  obtain ⟨N,U,r,cn,unit,uo,ku,rp,tube⟩ := original_generating_core_has_normal_tube s C
  have embed : IsClosedEmbedding s.euclideanPosition :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding
  let T := fun a : s.carrier × ℝ => s.euclideanPosition a.1+a.2 • N a.1
  have ct : Continuous T := (embed.continuous.comp continuous_fst).add (continuous_snd.smul (cn.comp continuous_fst))
  obtain ⟨R,positive,_,thin,cover⟩ := convergent_embedded_core_tube_exhaustion embed ct (fun _ => by simp [T]) vo ne
    (kc.of_isClosed_subset isClosed_closure sub) uo (fun p hp => ku p (sub hp)) rp tube closed conv
  exact ⟨N,R,cn,unit,positive,thin,cover⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_generating_core_convergent_sheets
