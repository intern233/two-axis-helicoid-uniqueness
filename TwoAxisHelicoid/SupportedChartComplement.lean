module

public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FunProp

public section

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

private noncomputable def chartComplementMap {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) (f : E → E) (x : M) : M := by
  classical
  exact if x∈e.source then e.symm (f (e x)) else x

private theorem chartComplement_map_data {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) {K A B : Set M} {U V : Set E} (kc : IsClosed K) (ks : K⊆e.source)
    (ao : ∀ x∈e.source, x∈A ↔ e x∈U) (bo : ∀ x∈e.source, x∈B ↔ e x∈V)
    (outside : ∀ x∉e.source, x∈A → x∈B) (uo : IsOpen U) (f : E → E) (cf : ContinuousOn f U)
    (maps : ∀ z∈e.target, z∈U → f z∈e.target ∩ V)
    (fixed : ∀ x∈e.source, x∈A → x∉K → f (e x)=e x) :
    MapsTo (chartComplementMap e f) A B ∧ ContinuousOn (chartComplementMap e f) A := by
  classical
  constructor
  · intro x hx
    by_cases hs : x∈e.source
    · have m := maps _ (e.map_source hs) ((ao x hs).mp hx)
      rw [chartComplementMap,ite_eq_left hs]
      apply (bo _ (e.map_target m.1)).mpr
      rw [e.right_inv m.1]
      exact m.2
    · simpa only [chartComplementMap,ite_eq_right hs] using outside x hs hx
  · intro x hx
    by_cases hs : x∈e.source
    · have hu := (ao x hs).mp hx
      have target := (maps _ (e.map_source hs) hu).1
      have df : ContinuousAt (fun w : M => f (e w)) x :=
        (cf.continuousAt (uo.mem_nhds hu)).comp (e.continuousAt hs)
      have d : ContinuousAt (fun w : M => e.symm (f (e w))) x :=
        (e.symm.continuousAt target).comp (f := fun w : M => f (e w)) df
      apply (d.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hs] with w hw
      simp only [chartComplementMap,ite_eq_left hw]
    · have no : x∉K := fun k => hs (ks k)
      have germ : chartComplementMap e f=ᶠ[𝓝[A] x] id := by
        filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (kc.isOpen_compl.mem_nhds no)] with w wa wk
        by_cases sw : w∈e.source
        · simp only [chartComplementMap,ite_eq_left sw,fixed w sw wa wk,e.left_inv sw,id_eq]
        · simp only [chartComplementMap,ite_eq_right sw,id_eq]
      exact continuousWithinAt_id.congr_of_eventuallyEq germ (by simp [chartComplementMap,hs])

/-- Glue a homeomorphism of two open portions of a coordinate chart to
the identity off a closed set inside the chart. The domain and target
on the ambient surface may be different deleted sets. -/
theorem supported_chart_complement_homeomorphism {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) {K A B : Set M} {U V : Set E}
    (kc : IsClosed K) (ks : K⊆e.source)
    (ao : ∀ x∈e.source, x∈A ↔ e x∈U) (bo : ∀ x∈e.source, x∈B ↔ e x∈V)
    (outside : ∀ x∉e.source, x∈A ↔ x∈B) (uo : IsOpen U) (vo : IsOpen V)
    (H : U ≃ₜ V)
    (fTarget : ∀ z : U, z.1∈e.target → (H z).1∈e.target)
    (gTarget : ∀ z : V, z.1∈e.target → (H.symm z).1∈e.target)
    (fFix : ∀ x (hs : x∈e.source) (ha : x∈A), x∉K → (H ⟨e x,(ao x hs).mp ha⟩).1=e x)
    (gFix : ∀ x (hs : x∈e.source) (hb : x∈B), x∉K → (H.symm ⟨e x,(bo x hs).mp hb⟩).1=e x) :
    Nonempty (A ≃ₜ B) := by
  classical
  let f (z : E) := if h : z∈U then (H ⟨z,h⟩).1 else z
  let g (z : E) := if h : z∈V then (H.symm ⟨z,h⟩).1 else z
  have forward (z : E) (hz : z∈U) : f z=(H ⟨z,hz⟩).1 := dite_eq_left hz
  have back (z : E) (hz : z∈V) : g z=(H.symm ⟨z,hz⟩).1 := dite_eq_left hz
  have cf : ContinuousOn f U := continuousOn_iff_continuous_domRestrict.mpr (by
    convert continuous_subtype_val.comp H.continuous using 1
    funext z
    exact forward z z.2)
  have cg : ContinuousOn g V := continuousOn_iff_continuous_domRestrict.mpr (by
    convert continuous_subtype_val.comp H.symm.continuous using 1
    funext z
    exact back z z.2)
  have fm (z : E) (ht : z∈e.target) (hz : z∈U) : f z∈e.target ∩ V := by
    rw [forward z hz]
    exact ⟨fTarget ⟨z,hz⟩ ht,(H ⟨z,hz⟩).2⟩
  have gm (z : E) (ht : z∈e.target) (hz : z∈V) : g z∈e.target ∩ U := by
    rw [back z hz]
    exact ⟨gTarget ⟨z,hz⟩ ht,(H.symm ⟨z,hz⟩).2⟩
  obtain ⟨mf,cF⟩ := chartComplement_map_data e kc ks ao bo (fun x h => (outside x h).mp) uo f cf fm
    (fun x hs ha hk => (forward _ ((ao x hs).mp ha)).trans (fFix x hs ha hk))
  obtain ⟨mg,cG⟩ := chartComplement_map_data e kc ks bo ao (fun x h => (outside x h).mpr) vo g cg gm
    (fun x hs hb hk => (back _ ((bo x hs).mp hb)).trans (gFix x hs hb hk))
  let F (x : A) : B := ⟨chartComplementMap e f x,mf x.2⟩
  let G (x : B) : A := ⟨chartComplementMap e g x,mg x.2⟩
  refine ⟨{
    toFun := F
    invFun := G
    continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp cF).subtype_mk _
    continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp cG).subtype_mk _
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro x
    apply Subtype.ext
    change chartComplementMap e g (chartComplementMap e f x.1)=x.1
    by_cases hs : x.1∈e.source
    · have hu := (ao _ hs).mp x.2
      have ht := (fm _ (e.map_source hs) hu).1
      simp only [chartComplementMap,ite_eq_left hs,ite_eq_left (e.map_target ht),e.right_inv ht]
      rw [forward _ hu,back _ (H ⟨e x,hu⟩).2]
      exact (congrArg e.symm (congrArg Subtype.val (H.symm_apply_apply ⟨e x,hu⟩))).trans (e.left_inv hs)
    · simp [chartComplementMap,hs]
  · intro x
    apply Subtype.ext
    change chartComplementMap e f (chartComplementMap e g x.1)=x.1
    by_cases hs : x.1∈e.source
    · have hv := (bo _ hs).mp x.2
      have ht := (gm _ (e.map_source hs) hv).1
      simp only [chartComplementMap,ite_eq_left hs,ite_eq_left (e.map_target ht),e.right_inv ht]
      rw [back _ hv,forward _ (H.symm ⟨e x,hv⟩).2]
      exact (congrArg e.symm (congrArg Subtype.val (H.apply_symm_apply ⟨e x,hv⟩))).trans (e.left_inv hs)
    · simp [chartComplementMap,hs]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.supported_chart_complement_homeomorphism
