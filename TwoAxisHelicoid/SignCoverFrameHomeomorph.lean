import TwoAxisHelicoid.SpinorFramePullback

namespace TwoAxisHelicoid
open Set Topology

theorem prod_fst_isLocalHomeomorph_of_discrete {X D : Type*}
    [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D] :
    IsLocalHomeomorph (Prod.fst : X × D → X) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro q
  let S : Set (X × D) := {v | v.2 = q.2}
  have hS : IsOpen S := (isOpen_discrete {q.2}).preimage continuous_snd
  refine ⟨S,hS.mem_nhds rfl,?_⟩
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_fst.comp continuous_subtype_val
  · intro r s hrs
    apply Subtype.ext
    exact Prod.ext hrs (r.2.trans s.2.symm)
  · exact isOpenMap_fst.comp hS.isOpenMap_subtype_val

theorem spinorFramePullbackMk_isLocalHomeomorph (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (s : PuncturedLatticePlane L → UnitSpinor)
    (hs : UnitSpinorEquivariant L χ s) (hc : Continuous s) :
    IsLocalHomeomorph (spinorFramePullbackMk L χ s hs) := by
  have hbase := (puncturedPlaneProjection_isLocalHomeomorph L).comp
    (prod_fst_isLocalHomeomorph_of_discrete (X := PuncturedLatticePlane L) (D := ZMod 2))
  have hproj := coverPullbackProjection_isLocalHomeomorph
    (equivariantTorusFrame_continuous L χ s hs hc)
    unitSpinorTangentFrame_isCoveringMap.isLocalHomeomorph
  change IsLocalHomeomorph (coverPullbackProjection (equivariantTorusFrame L s)
    unitSpinorTangentFrame ∘ spinorFramePullbackMk L χ s hs) at hbase
  exact hbase.of_comp hproj (spinorFramePullbackMk_continuous L χ s hs hc)

noncomputable def signCoverToFramePullback (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s) :
    PuncturedSignCover L χ → TorusFramePullback L s :=
  quotientFiberDescend (puncturedSignCoverMk L χ) (puncturedSignCoverMk_surjective L χ)
    (spinorFramePullbackMk L χ s hs)

theorem signCoverToFramePullback_mk (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s)
    (v : PuncturedLatticePlane L × ZMod 2) :
    signCoverToFramePullback L χ s hs (puncturedSignCoverMk L χ v) =
      spinorFramePullbackMk L χ s hs v :=
  quotientFiberDescend_apply _ _ _ (fun v w => (spinorFramePullbackMk_fibers L χ s hs v w).mpr) v

theorem signCoverToFramePullback_bijective (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s) :
    Function.Bijective (signCoverToFramePullback L χ s hs) := by
  constructor
  · intro q r hqr
    obtain ⟨v,rfl⟩ := puncturedSignCoverMk_surjective L χ q
    obtain ⟨w,rfl⟩ := puncturedSignCoverMk_surjective L χ r
    rw [signCoverToFramePullback_mk,signCoverToFramePullback_mk] at hqr
    exact (spinorFramePullbackMk_fibers L χ s hs v w).mp hqr
  · intro q
    obtain ⟨v,hv⟩ := spinorFramePullbackMk_surjective L χ s hs q
    exact ⟨puncturedSignCoverMk L χ v,(signCoverToFramePullback_mk L χ s hs v).trans hv⟩

theorem signCoverToFramePullback_continuous (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s)
    (hc : Continuous s) : Continuous (signCoverToFramePullback L χ s hs) :=
  quotientFiberDescend_continuous (puncturedSignCoverMk_isQuotientMap L χ) _
    (fun v w => (spinorFramePullbackMk_fibers L χ s hs v w).mpr)
    (spinorFramePullbackMk_continuous L χ s hs hc)

theorem signCoverToFramePullback_isOpenMap (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s)
    (hc : Continuous s) : IsOpenMap (signCoverToFramePullback L χ s hs) := by
  apply IsOpenMap.of_comp (puncturedSignCoverMk_continuous L χ)
    (puncturedSignCoverMk_surjective L χ)
  have he : signCoverToFramePullback L χ s hs ∘ puncturedSignCoverMk L χ =
      spinorFramePullbackMk L χ s hs :=
    funext (signCoverToFramePullback_mk L χ s hs)
  rw [he]
  exact (spinorFramePullbackMk_isLocalHomeomorph L χ s hs hc).isOpenMap

/-- The flat sign cover is identified with the actual pullback of the
spinor double cover of orthonormal tangent frames. Both directions are
continuous; this is stronger than an equality of period characters. -/
noncomputable def signCoverFramePullbackHomeomorph (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (s : PuncturedLatticePlane L → UnitSpinor)
    (hs : UnitSpinorEquivariant L χ s) (hc : Continuous s) :
    PuncturedSignCover L χ ≃ₜ TorusFramePullback L s :=
  (Equiv.ofBijective (signCoverToFramePullback L χ s hs)
    (signCoverToFramePullback_bijective L χ s hs)).toHomeomorphOfContinuousOpen
      (signCoverToFramePullback_continuous L χ s hs hc)
      (signCoverToFramePullback_isOpenMap L χ s hs hc)

theorem signCoverFramePullbackHomeomorph_over_base (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (s : PuncturedLatticePlane L → UnitSpinor)
    (hs : UnitSpinorEquivariant L χ s) (hc : Continuous s) (q : PuncturedSignCover L χ) :
    (signCoverFramePullbackHomeomorph L χ s hs hc q).1.1 = puncturedSignCoverProjection L χ q := by
  obtain ⟨v,rfl⟩ := puncturedSignCoverMk_surjective L χ q
  change (signCoverToFramePullback L χ s hs (puncturedSignCoverMk L χ v)).1.1 = _
  rw [signCoverToFramePullback_mk]
  rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.signCoverFramePullbackHomeomorph
#print axioms TwoAxisHelicoid.signCoverFramePullbackHomeomorph_over_base

