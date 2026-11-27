import TwoAxisHelicoid.CompactSpinPlaneCover
import TwoAxisHelicoid.MultiplierSpinRestriction

namespace TwoAxisHelicoid
open Set Topology
set_option maxHeartbeats 1000000

variable (L : PeriodPair) (χ : L.lattice →+ ZMod 2)

noncomputable def puncturedCompactSpinPlaneMk (v : PuncturedLatticePlane L × ℝ) :
    RestrictedCompactMultiplierSpin L χ :=
  ⟨compactSpinPlaneMk L χ (v.1.1,v.2),fun h => v.1.2 ((periodTorusProjection_eq_zero L v.1.1).mp h)⟩

theorem puncturedCompactSpinPlaneMk_continuous : Continuous (puncturedCompactSpinPlaneMk L χ) :=
  ((compactSpinPlaneMk_isOpenQuotientMap L χ).continuous.comp
    (f := Prod.map (Subtype.val : PuncturedLatticePlane L → ℂ) (id : ℝ → ℝ))
    (continuous_subtype_val.prodMap continuous_id)).subtype_mk _

/-- A continuous map over the frame projection into an arbitrary
covering of T × S¹ extends uniquely across the entire missing circle.
Lifts are constructed on the simply connected plane of parameters and
real angles and compared on its connected punctured restriction. -/
theorem punctured_full_spin_map_extends
    {E : Type*} [TopologicalSpace E] {p : E → PeriodTorus L × Circle} (hp : IsCoveringMap p)
    (f : C(RestrictedCompactMultiplierSpin L χ,E))
    (hf : ∀ s, p (f s) = compactMultiplierSpinProjection L χ s.1) :
    ∃! F : C(CompactMultiplierSpinBundle L χ,E),
      (∀ s, p (F s) = compactMultiplierSpinProjection L χ s) ∧
      ∀ s : RestrictedCompactMultiplierSpin L χ, F s.1 = f s := by
  let P := compactSpinPlaneMk L χ
  let π := compactMultiplierSpinProjection L χ
  have hP := compactSpinPlaneMk_isOpenQuotientMap L χ
  let base : C(ℂ × ℝ,PeriodTorus L × Circle) :=
    ⟨π ∘ P,(compactMultiplierSpinProjection_isCoveringMap L χ).continuous.comp hP.continuous⟩
  let z₀ : PuncturedLatticePlane L := puncturedBasisLine L 0 0
  let u₀ : PuncturedLatticePlane L × ℝ := (z₀,0)
  let i : PuncturedLatticePlane L × ℝ → ℂ × ℝ := Prod.map Subtype.val id
  have hi : Continuous i := continuous_subtype_val.prodMap continuous_id
  let R := puncturedCompactSpinPlaneMk L χ
  obtain ⟨G,⟨hG0,hGbase⟩,_⟩ := hp.existsUnique_continuousMap_lifts base (i u₀)
    (f (R u₀)) (hf (R u₀))
  have hGp (v : ℂ × ℝ) : p (G v) = π (P v) := congrFun hGbase v
  let := puncturedLatticePlane_connectedSpace L
  have hGr : G ∘ i = f ∘ R := by
    exact hp.eq_of_comp_eq (G.continuous.comp hi)
      (f.continuous.comp (puncturedCompactSpinPlaneMk_continuous L χ))
      (funext fun v => (hGp (i v)).trans (hf (R v)).symm) u₀ hG0
  have hGfiber (v w : ℂ × ℝ) (he : P v = P w) : G v = G w := by
    let k : ℂ × ℝ := (z₀.1-v.1,0)
    have hv : (v+k).1 ∉ L.lattice := by
      change v.1+(z₀.1-v.1) ∉ L.lattice
      simpa only [add_sub_cancel] using z₀.2
    have he' := compactSpinPlaneMk_eq_translate L χ he k
    have hbase : periodTorusProjection L (v+k).1 = periodTorusProjection L (w+k).1 :=
      congrArg (fun s => (π s).1) he'
    have hw : (w+k).1 ∉ L.lattice := fun hh =>
      hv ((periodTorusProjection_eq_zero L _).mp (hbase.trans ((periodTorusProjection_eq_zero L _).mpr hh)))
    let v' : PuncturedLatticePlane L × ℝ := (⟨(v+k).1,hv⟩,(v+k).2)
    let w' : PuncturedLatticePlane L × ℝ := (⟨(w+k).1,hw⟩,(w+k).2)
    have he0 : G (v+k) = G (w+k) :=
      (congrFun hGr v').trans ((congrArg f (show R v' = R w' from Subtype.ext he')).trans
        (congrFun hGr w').symm)
    have heG : (fun a : ℂ × ℝ => G (v+a)) = fun a => G (w+a) := by
      exact hp.eq_of_comp_eq (G.continuous.comp (continuous_const.add continuous_id))
        (G.continuous.comp (continuous_const.add continuous_id))
        (funext fun a => (hGp (v+a)).trans ((congrArg π (compactSpinPlaneMk_eq_translate L χ he a)).trans
          (hGp (w+a)).symm)) k he0
    simpa only [add_zero] using congrFun heG 0
  let F : C(CompactMultiplierSpinBundle L χ,E) :=
    ⟨quotientFiberDescend P hP.surjective G,
      quotientFiberDescend_continuous hP.isQuotientMap G hGfiber G.continuous⟩
  have hFmk (v : ℂ × ℝ) : F (P v) = G v := quotientFiberDescend_apply _ _ G hGfiber v
  have hFp (s) : p (F s) = π s := by
    obtain ⟨v,rfl⟩ := hP.surjective s
    exact (congrArg p (hFmk v)).trans (hGp v)
  have hFr (s : RestrictedCompactMultiplierSpin L χ) : F s.1 = f s := by
    obtain ⟨v,hv⟩ := hP.surjective s.1
    have hz : v.1 ∉ L.lattice := fun hz => s.2 ((congrArg (fun s => (π s).1) hv).symm.trans
      ((periodTorusProjection_eq_zero L v.1).mpr hz))
    let u : PuncturedLatticePlane L × ℝ := (⟨v.1,hz⟩,v.2)
    exact (congrArg F hv.symm).trans ((hFmk v).trans ((congrFun hGr u).trans
      (congrArg f (show R u = s from Subtype.ext hv))))
  refine ⟨F,⟨hFp,hFr⟩,?_⟩
  intro H hH
  let : PathConnectedSpace (CompactMultiplierSpinBundle L χ) := hP.surjective.pathConnectedSpace hP.continuous
  apply ContinuousMap.ext
  exact congrFun (hp.eq_of_comp_eq H.continuous F.continuous
    (funext fun s => (hH.1 s).trans (hFp s).symm) (R u₀).1 ((hH.2 (R u₀)).trans (hFr (R u₀)).symm))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_full_spin_map_extends
