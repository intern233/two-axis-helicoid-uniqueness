import TwoAxisHelicoid.SpinGeneratorCoreRetraction
import TwoAxisHelicoid.TorusGeneratorIntersections
import TwoAxisHelicoid.TorusQuaternionLiftCriterion
import TwoAxisHelicoid.SpinCommutatorMonodromy

namespace TwoAxisHelicoid
open Set Topology

private noncomputable def reduceEndpoint (t : unitInterval) : unitInterval := if t = 1 then 0 else t

private theorem reduceEndpoint_mem (t : unitInterval) : (reduceEndpoint t : ℝ) ∈ Ico (0 : ℝ) 1 := by
  by_cases h : t = 1
  · simp [reduceEndpoint,h]
  · simpa [reduceEndpoint,h] using And.intro t.2.1 (lt_of_le_of_ne t.2.2 (fun e => h (Subtype.ext e)))

private theorem reduceEndpoint_eq {A : Type*} (f : unitInterval → A) (hf : f 1 = f 0) (t : unitInterval) :
    f t = f (reduceEndpoint t) := by
  by_cases h : t = 1
  · simpa [reduceEndpoint,h] using hf
  · simp [reduceEndpoint,h]

noncomputable def spinCoreLoopMap (L : PeriodPair) (i : Fin 2) (s : unitInterval) : puncturedGeneratorCore L :=
  ⟨puncturedTorusGeneratorLoop L i s,puncturedTorusGeneratorLoop_mem_core L i s⟩

private theorem spinCoreLoopMap_eq {L : PeriodPair} {i : Fin 2} {t s : unitInterval}
    (h : spinCoreLoopMap L i t = spinCoreLoopMap L i s) : reduceEndpoint t = reduceEndpoint s := by
  have he := congrArg Subtype.val h
  have hend := (puncturedTorusGeneratorLoop L i).target.trans (puncturedTorusGeneratorLoop L i).source.symm
  have h := ((reduceEndpoint_eq _ hend t).symm.trans he).trans (reduceEndpoint_eq _ hend s)
  exact Subtype.ext (puncturedBasisLine_projection_injOn L i (reduceEndpoint_mem t) (reduceEndpoint_mem s) h)

private theorem spinCoreLoopMap_inter {L : PeriodPair} {t s : unitInterval}
    (h : spinCoreLoopMap L 0 t = spinCoreLoopMap L 1 s) : reduceEndpoint t = 0 ∧ reduceEndpoint s = 0 := by
  have he := congrArg Subtype.val h
  have hend (i : Fin 2) := (puncturedTorusGeneratorLoop L i).target.trans (puncturedTorusGeneratorLoop L i).source.symm
  have h := ((reduceEndpoint_eq _ (hend 0) t).symm.trans he).trans (reduceEndpoint_eq _ (hend 1) s)
  obtain ⟨ht,hs⟩ := puncturedBasisLines_intersection L (reduceEndpoint_mem t) (reduceEndpoint_mem s) h
  exact ⟨Subtype.ext ht,Subtype.ext hs⟩

/-- Continuous closed lifts on the actual two marked loops, agreeing at their
basepoint, descend to a continuous map on their union in the quotient torus. -/
theorem punctured_generator_glue {A : Type*} [TopologicalSpace A] (L : PeriodPair) (a b : C(unitInterval,A))
    (ha : a 1 = a 0) (hb : b 1 = b 0) (hab : a 0 = b 0) :
    ∃ f : C(puncturedGeneratorCore L,A), (∀ t, f (spinCoreLoopMap L 0 t) = a t) ∧
      ∀ t, f (spinCoreLoopMap L 1 t) = b t := by
  let p : unitInterval ⊕ unitInterval → puncturedGeneratorCore L := Sum.elim (spinCoreLoopMap L 0) (spinCoreLoopMap L 1)
  let g : unitInterval ⊕ unitInterval → A := Sum.elim a b
  have hc (i : Fin 2) : Continuous (spinCoreLoopMap L i) := (puncturedTorusGeneratorLoop L i).continuous.subtype_mk _
  have hq : IsQuotientMap p := IsQuotientMap.of_surjective_continuous (by
    intro x
    rcases x.2 with ⟨t,ht⟩ | ⟨t,ht⟩
    · exact ⟨Sum.inl t,Subtype.ext ht⟩
    · exact ⟨Sum.inr t,Subtype.ext ht⟩) ((hc 0).sumElim (hc 1))
  have hinter {s t : unitInterval} (h : spinCoreLoopMap L 0 s = spinCoreLoopMap L 1 t) : a s = b t := by
    obtain ⟨hs,ht⟩ := spinCoreLoopMap_inter h
    rw [reduceEndpoint_eq a ha s,reduceEndpoint_eq b hb t,hs,ht,hab]
  have hfib : ∀ x y, p x = p y → g x = g y := by
    rintro (s|s) (t|t) h
    · exact ((reduceEndpoint_eq a ha s).trans (congrArg a (spinCoreLoopMap_eq h))).trans (reduceEndpoint_eq a ha t).symm
    · exact hinter h
    · exact (hinter h.symm).symm
    · exact ((reduceEndpoint_eq b hb s).trans (congrArg b (spinCoreLoopMap_eq h))).trans (reduceEndpoint_eq b hb t).symm
  let f : C(puncturedGeneratorCore L,A) := ⟨quotientFiberDescend p hq.surjective g,
    quotientFiberDescend_continuous hq g hfib (a.continuous.sumElim b.continuous)⟩
  exact ⟨f,fun t => quotientFiberDescend_apply p hq.surjective g hfib (.inl t),
    fun t => quotientFiberDescend_apply p hq.surjective g hfib (.inr t)⟩

/-- The actual two generator frame curves detect whether a continuous
quaternion lift exists everywhere on the entire punctured marked torus. -/
theorem punctured_frame_global_lift_iff (L : PeriodPair) (F : C(PuncturedPeriodTorus L,OrthonormalTangentPair)) :
    (∃ q : C(PuncturedPeriodTorus L,UnitQuaternion), ∀ x, unitQuaternionFrame (q x) = F x) ↔
      ∀ i, SpatialFrameCurveCloses (fun t => F (puncturedTorusGeneratorLoop L i t)) := by
  constructor
  · rintro ⟨q,hq⟩ i
    let γ := puncturedTorusGeneratorLoop L i
    exact ⟨q.comp γ.toContinuousMap,congrArg q (γ.target.trans γ.source.symm),fun t => hq _⟩
  intro ha
  obtain ⟨a,hae,haF⟩ := ha 0
  obtain ⟨b,hbe,hbF⟩ := ha 1
  have hbase : unitQuaternionFrame (a 0) = unitQuaternionFrame (b 0) :=
    (haF 0).trans ((congrArg F ((puncturedTorusGeneratorLoop L 0).source.trans
      (puncturedTorusGeneratorLoop L 1).source.symm)).trans (hbF 0).symm)
  have hb : ∃ c : C(unitInterval,UnitQuaternion), c 1 = c 0 ∧ a 0 = c 0 ∧
      ∀ t, unitQuaternionFrame (c t) = F (puncturedTorusGeneratorLoop L 1 t) := by
    rcases unitQuaternionFrame_fibers.mp hbase with he|he
    · exact ⟨b,hbe,Subtype.ext he,hbF⟩
    · let c : C(unitInterval,UnitQuaternion) := ⟨fun t => unitQuaternionAntipode (b t),
        unitQuaternionAntipode.continuous.comp b.continuous⟩
      exact ⟨c,congrArg unitQuaternionAntipode hbe,Subtype.ext (he.trans (unitQuaternionAntipode_val (b 0)).symm),fun t => (unitQuaternionFrame_antipode _).trans (hbF t)⟩
  obtain ⟨c,hce,hac,hcF⟩ := hb
  obtain ⟨f,hfa,hfc⟩ := punctured_generator_glue L a c hae hce hac
  have hf (x : puncturedGeneratorCore L) : unitQuaternionFrame (f x) = F x.1 := by
    rcases x.2 with ⟨t,ht⟩ | ⟨t,ht⟩
    · rw [← (show spinCoreLoopMap L 0 t = x from Subtype.ext ht),hfa]; exact haF t
    · rw [← (show spinCoreLoopMap L 1 t = x from Subtype.ext ht),hfc]; exact hcF t
  let R := puncturedMarkedGeneratorRetraction L
  let r : C(PuncturedPeriodTorus L,puncturedGeneratorCore L) := ⟨fun x => ⟨R.flow (1,x),R.terminal x⟩,
    (R.flow.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let h : C(unitInterval × PuncturedPeriodTorus L,OrthonormalTangentPair) := F.comp
    (R.flow.comp ⟨fun z => (unitInterval.symm z.1,z.2),(unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd⟩)
  have hzero (x) : h (0,x) = unitQuaternionFrame ((f.comp r) x) := by
    change F (R.flow (unitInterval.symm 0,x)) = unitQuaternionFrame (f (r x))
    rw [unitInterval.symm_zero]; exact (hf (r x)).symm
  let q := unitQuaternionFrame_isCoveringMap.liftHomotopy h (f.comp r) hzero
  refine ⟨⟨fun x => q (1,x),q.continuous.comp (continuous_const.prodMk continuous_id)⟩,fun x => ?_⟩
  have hq := congrFun (unitQuaternionFrame_isCoveringMap.liftHomotopy_lifts h (f.comp r) hzero) (1,x)
  change unitQuaternionFrame (q (1,x)) = F (R.flow (unitInterval.symm 1,x)) at hq
  change unitQuaternionFrame (q (1,x)) = F x
  simpa only [unitInterval.symm_one,R.initial] using hq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_frame_global_lift_iff
