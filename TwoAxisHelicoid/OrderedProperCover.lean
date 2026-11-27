import TwoAxisHelicoid.ProperLocalCover
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

def lowestFiberPoints {E X : Type*} (f : E → X) (h : E → ℝ) : Set E :=
  {e | ∀ d, f d = f e → h e ≤ h d}

theorem lowestFiberPoints_isClosed {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {h : E → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hl : IsLocalHomeomorph f) : IsClosed (lowestFiberPoints f h) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro e he
  change ¬ (∀ d, f d = f e → h e ≤ h d) at he
  push Not at he
  obtain ⟨d,hde,hdh⟩ := he
  obtain ⟨φ,hd,hφ⟩ := hl d
  have hfe : f e ∈ φ.target := by rw [← hde,hφ]; exact φ.map_source hd
  have hback : φ.symm (f e) = d := by rw [← hde,hφ]; exact φ.left_inv hd
  have hch : ContinuousAt (fun q => h (φ.symm (f q))) e :=
    hh.continuousAt.comp ((φ.continuousAt_symm hfe).comp hf.continuousAt)
  have hlt : ∀ᶠ q in 𝓝 e, h (φ.symm (f q)) < h q := by
    have hn : ∀ᶠ z : ℝ × ℝ in 𝓝 (h (φ.symm (f e)),h e), z.1 < z.2 :=
      (isOpen_lt continuous_fst continuous_snd).mem_nhds (by
        change h (φ.symm (f e)) < h e
        simpa only [hback] using hdh)
    exact (hch.prodMk hh.continuousAt).eventually hn
  filter_upwards [hlt,hf.continuousAt.eventually (φ.open_target.mem_nhds hfe)] with q hq hqt
  intro hmin
  have hsame : f (φ.symm (f q)) = f q := by
    calc
      _ = φ (φ.symm (f q)) := congrFun hφ _
      _ = f q := φ.right_inv hqt
  exact hq.not_ge (hmin _ hsame)

theorem lowestFiberPoints_isOpen {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {h : E → ℝ} (hp : IsProperMap f) (hh : Continuous h)
    (hl : IsLocalHomeomorph f)
    (hsep : ∀ d e, f d = f e → h d = h e → d = e) : IsOpen (lowestFiberPoints f h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro e he
  obtain ⟨φ,hφe,hφ⟩ := hl e
  let K := (f ⁻¹' {f e}) ∩ φ.sourceᶜ
  have hK : IsCompact K :=
    (hp.isCompact_preimage isCompact_singleton).inter_right φ.open_source.isClosed_compl
  have hstrict : ∀ d ∈ K, h e < h d := by
    intro d hd
    have hde : f d = f e := hd.1
    refine lt_of_le_of_ne (he d hde) ?_
    intro heq
    have hsame := hsep d e hde heq.symm
    exact hd.2 (hsame.symm ▸ hφe)
  obtain ⟨c,hec,hc⟩ := hK.exists_forall_le' hh.continuousOn hstrict
  let b := (h e+c)/2
  have heb : h e < b := by dsimp [b]; linarith
  have hbc : b < c := by dsimp [b]; linarith
  let B := φ.sourceᶜ ∩ {d | h d ≤ b}
  have hB : IsClosed B := φ.open_source.isClosed_compl.inter (isClosed_le hh continuous_const)
  have hnot : f e ∉ f '' B := by
    rintro ⟨d,hd,hde⟩
    have hdc := hc d ⟨hde,hd.1⟩
    exact hbc.not_ge (hdc.trans hd.2)
  have hN : (f '' B)ᶜ ∈ 𝓝 (f e) := (hp.isClosedMap B hB).isOpen_compl.mem_nhds hnot
  have hheight : ∀ᶠ q in 𝓝 e, h q < b := hh.continuousAt.eventually (Iio_mem_nhds heb)
  filter_upwards [φ.open_source.mem_nhds hφe,hp.continuous.continuousAt.eventually hN,hheight]
    with q hqU hqB hqb
  intro d hd
  by_contra hfail
  have hdh : h d < h q := lt_of_not_ge hfail
  have hdU : d ∈ φ.source := by
    by_contra hn
    exact hqB ⟨d,⟨hn,(hdh.trans hqb).le⟩,hd⟩
  have hsame : d = q := φ.injOn hdU hqU (by rw [← hφ]; exact hd)
  subst d
  exact lt_irrefl _ hdh

/-- A connected proper local homeomorphism whose fibers are separated by
a continuous real height is injective. This proves the global one-sheet
conclusion for a connected ordered cover, rather than assuming that its
monodromy is trivial. -/
theorem connected_ordered_proper_local_homeomorph_injective {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace E]
    {f : E → X} {h : E → ℝ} (hp : IsProperMap f) (hh : Continuous h)
    (hl : IsLocalHomeomorph f)
    (hsep : ∀ d e, f d = f e → h d = h e → d = e) : Function.Injective f := by
  intro d e hde
  have hc : IsClopen (lowestFiberPoints f h) :=
    ⟨lowestFiberPoints_isClosed hp.continuous hh hl,lowestFiberPoints_isOpen hp hh hl hsep⟩
  have hne : (lowestFiberPoints f h).Nonempty := by
    obtain ⟨q,hq,hmin⟩ := (hp.isCompact_preimage (K := {f d}) isCompact_singleton).exists_isMinOn
      (show (f ⁻¹' {f d}).Nonempty from ⟨d,rfl⟩) hh.continuousOn
    refine ⟨q,?_⟩
    intro z hz
    exact hmin (hz.trans hq)
  have hall := hc.eq_univ hne
  have hd : d ∈ lowestFiberPoints f h := by rw [hall]; trivial
  have he : e ∈ lowestFiberPoints f h := by rw [hall]; trivial
  exact hsep d e hde (le_antisymm (hd e hde.symm) (he d hde))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.connected_ordered_proper_local_homeomorph_injective
