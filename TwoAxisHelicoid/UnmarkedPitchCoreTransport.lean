import TwoAxisHelicoid.MarkedCoreCoveringConvergence
import TwoAxisHelicoid.PhysicalAppendixBCompactness

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

/-- Local convergence of the unmarked physical point--normal sets,
together with a regular period marking of the *limit alone*, produces
smooth open torus maps and locally uniform C¹ convergence in the
covering plane. Moving marked charts and curve velocity estimates
are obtained from the actual physical embeddings. -/
theorem unmarked_pitch_core_transport (s : OriginalSmoothHelicoid) {A : PeriodPair}
    (m : s.carrier ≃ₜ PuncturedPeriodTorus A) (Y : PeriodTorus A → Fin 3 → ℝ)
    (pos : ∀ x, Y (m x).1=s.position x)
    (regular : ∀ z∉A.lattice, ContDiffAt ℝ ∞ (Y ∘ periodTorusProjection A) z ∧
      Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection A) z))
    (W : ℕ → PitchNormalizedBasicImmersion) (mem : ∀ n, W n∈embeddedPitchFamily)
    (moving : ℕ → OriginalHelicoidRepresentative) (same : ∀ n, (moving n).image=(W n).image)
    (conv : LocalSpatialImageLimit (fun n => (moving n).unorientedNormals) s.unorientedNormals)
    (C : TorusGeneratingCoreModel A) :
    ∃ k : ℕ, ∃ F : ∀ n, SmoothOpenTorusCoreMap C (rhombicPeriodPair (W (n+k)).t (W (n+k)).ht),
      let Z := fun n => (W (n+k)).torusPosition ∘ (F n).map ∘ periodTorusProjection A
      let Z₀ := coordinateToEuclidean ∘ Y ∘ periodTorusProjection A
      let U := periodTorusProjection A ⁻¹' C.carrier
      (∀ n z, z∈U → DifferentiableAt ℝ (Z n) z) ∧ (∀ z∈U, ContDiffAt ℝ 1 Z₀ z) ∧
        TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ Z₀) atTop U := by
  let t : OriginalSmoothHelicoid := {s with modelTorus := A, topologicalType := m}
  let V := {b : s.carrier | (m b).1∈C.carrier}
  let U := periodTorusProjection A ⁻¹' C.carrier
  have uo : IsOpen U := C.isOpen_carrier.preimage QuotientAddGroup.continuous_mk
  obtain ⟨e,mark⟩ := covering_marking_core_equiv m C
  obtain ⟨N,r,_,_,_,k,b,G,_,charts⟩ :=
    original_unmarked_handles_converge_C1_on_core t C (fun n => (moving n).toOriginalSmoothHelicoid) conv
  let H := fun n => (moving (n+k)).euclideanPosition ∘ (G n).point
  let Z := fun n => H n ∘ e.symm ∘ coveringCoreParameter C
  obtain ⟨sm,der⟩ := marked_core_covering_C1 m C s.position Y pos regular e mark b H (by
    intro a reg
    obtain ⟨sc,_,dc⟩ := charts a reg
    exact ⟨fun n z hz => (sc n z hz).2,dc⟩)
  choose g loc using fun n => embedded_pitch_position_marking (W n) (mem n) (moving n) (same n)
  let σ := fun n => (g (n+k)).symm ∘ (G n).point ∘ e.symm
  have smooth (n : ℕ) := smooth_torus_core_of_plane_position C (W (n+k)) (mem (n+k)) (σ n)
    ((g (n+k)).symm.isOpenEmbedding.comp ((G n).open_point.comp e.symm.isOpenEmbedding)) (Z n) (sm n) (by
      intro q z hq
      have zq : coveringCoreParameter C z=q := Subtype.ext ((coveringCoreParameter_val C (hq ▸ q.2)).trans hq.symm)
      change (W (n+k)).torusPosition ((g (n+k)).symm ((G n).point (e.symm q))).1=H n (e.symm (coveringCoreParameter C z))
      rw [← loc,zq,(g (n+k)).apply_symm_apply]
      rfl)
  choose F f using smooth
  let P := fun n => (W (n+k)).torusPosition ∘ (F n).map ∘ periodTorusProjection A
  have eq (n : ℕ) (z : ℂ) (hz : z∈U) : P n z=Z n z := by
    let q := coveringCoreParameter C z
    have πq : q.1=periodTorusProjection A z := coveringCoreParameter_val C hz
    change (W (n+k)).torusPosition ((F n).map (periodTorusProjection A z))=H n (e.symm q)
    rw [← πq,f n q,← loc]
    change (moving (n+k)).euclideanPosition ((g (n+k)) ((g (n+k)).symm _))=_
    rw [(g (n+k)).apply_symm_apply]
    rfl
  have germ (n : ℕ) (z : ℂ) (hz : z∈U) : P n=ᶠ[𝓝 z] Z n :=
    Filter.mem_of_superset (uo.mem_nhds hz) (eq n)
  refine ⟨k,F,fun n z hz => ((sm n z hz).congr_of_eventuallyEq (germ n z hz)).differentiableAt one_ne_zero,?_,?_⟩
  · intro z hz
    have nz : z∉A.lattice := fun h => C.closure_avoids ((periodTorusProjection_eq_zero A z).mpr h ▸ subset_closure hz)
    exact coordinateToEuclidean.contDiff.contDiffAt.comp z ((regular z nz).1.of_le (by simp))
  · exact der.congr (fun n z hz => (germ n z hz).fderiv_eq.symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unmarked_pitch_core_transport
