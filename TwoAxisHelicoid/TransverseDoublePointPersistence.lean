import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff

/-- A transverse self-intersection of one member of a jointly C¹ family
persists for every nearby parameter. The two preimages can be taken in
arbitrarily prescribed neighborhoods. -/
theorem transverse_double_point_persists {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : ℝ × E → V) (t : ℝ) {a b : E} (hab : a ≠ b)
    (he : F (t,a) = F (t,b))
    (ha : ContDiffAt ℝ 1 F (t,a)) (hb : ContDiffAt ℝ 1 F (t,b))
    (transverse : ∀ y : V, ∃ u v : E,
      fderiv ℝ (fun z => F (t,z)) a u - fderiv ℝ (fun z => F (t,z)) b v = y)
    {U W : Set E} (hU : U ∈ 𝓝 a) (hW : W ∈ 𝓝 b) :
    ∀ᶠ s in 𝓝 t, ∃ u ∈ U, ∃ v ∈ W, u ≠ v ∧ F (s,u) = F (s,v) := by
  let T := ContinuousLinearMap.fst ℝ ℝ (E × E)
  let P := ContinuousLinearMap.snd ℝ ℝ (E × E)
  let A := (ContinuousLinearMap.fst ℝ E E).comp P
  let B := (ContinuousLinearMap.snd ℝ E E).comp P
  let j := ContinuousLinearMap.inr ℝ ℝ E
  let D := fderiv ℝ F (t,a)
  let H := fderiv ℝ F (t,b)
  let G := fun q : ℝ × (E × E) => (q.1,F (q.1,q.2.1)-F (q.1,q.2.2))
  let J := T.prod ((D.comp (T.prod A))-(H.comp (T.prod B)))
  let x : ℝ × (E × E) := (t,a,b)
  have hJ : HasStrictFDerivAt G J x :=
    T.hasStrictFDerivAt.prodMk ((ha.hasStrictFDerivAt one_ne_zero |>.comp x (T.prod A).hasStrictFDerivAt).sub
      (hb.hasStrictFDerivAt one_ne_zero |>.comp x (T.prod B).hasStrictFDerivAt))
  have slice (z : E) (h : ContDiffAt ℝ 1 F (t,z)) :
      fderiv ℝ (fun w => F (t,w)) z = (fderiv ℝ F (t,z)).comp j := by
    have hj : HasFDerivAt (fun w : E => (t,w)) j z :=
      (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
    exact ((h.differentiableAt one_ne_zero).hasFDerivAt.comp z hj).fderiv
  have onto : Function.Surjective J := by
    rintro ⟨s,y⟩
    obtain ⟨u,v,h⟩ := transverse (y - (D (s,0)-H (s,0)))
    rw [slice _ ha,slice _ hb] at h
    change D (0,u)-H (0,v) = _ at h
    refine ⟨(s,u,v),Prod.ext rfl ?_⟩
    change D (s,u)-H (s,v) = y
    have sum (w : E) : (s,w) = (s,0) + (0,w) := by simp
    rw [sum u, sum v, map_add, map_add]
    calc
      _ = (D (0,u)-H (0,v)) + (D (s,0)-H (s,0)) := by abel
      _ = y := eq_sub_iff_add_eq.mp h
  have image : Set.image G {q : ℝ × (E × E) | q.2.1 ∈ U ∧ q.2.2 ∈ W ∧ q.2.1 ≠ q.2.2} ∈ 𝓝 (t,(0:V)) := by
    have e : G x = (t,0) := Prod.ext rfl (sub_eq_zero.mpr he)
    rw [← e, ← hJ.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr onto)]
    apply Filter.image_mem_map
    have h₁ : ContinuousAt (fun q : ℝ × (E × E) => q.2.1) x := continuous_fst.continuousAt.comp continuous_snd.continuousAt
    have h₂ : ContinuousAt (fun q : ℝ × (E × E) => q.2.2) x := continuous_snd.continuousAt.comp continuous_snd.continuousAt
    filter_upwards [h₁ hU, h₂ hW, (h₁.ne_iff_eventually_ne h₂).mp hab] with q hu hw hn using ⟨hu,hw,hn⟩
  have line : ContinuousAt (fun s : ℝ => (s,(0:V))) t := continuousAt_id.prodMk continuousAt_const
  filter_upwards [line image] with s hs
  obtain ⟨⟨s',u,v⟩,⟨hu,hv,hne⟩,h⟩ := hs
  have ht : s' = s := congrArg Prod.fst h
  subst s'
  exact ⟨u,hu,v,hv,hne,sub_eq_zero.mp (congrArg Prod.snd h)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.transverse_double_point_persists
