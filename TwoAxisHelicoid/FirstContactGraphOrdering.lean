import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach

namespace TwoAxisHelicoid
open Filter Set Topology
open scoped ContDiff Topology

/-- Two continuous graph sheets over the same connected open patch can
only approach a first contact from one side. The ordering is deduced
from separation on a cofinal set of nearby parameters. -/
theorem graph_sheets_ordered_at_first_contact {E : Type*} [TopologicalSpace E]
    {U : Set E} (hU : IsPreconnected U) (f g : ℝ → E → ℝ) (t : ℝ)
    (hf : ∀ x ∈ U, ContinuousAt (fun s => f s x) t)
    (hg : ∀ x ∈ U, ContinuousAt (fun s => g s x) t)
    (hsep : ∃ᶠ s in 𝓝 t, ContinuousOn (f s) U ∧ ContinuousOn (g s) U ∧ ∀ x ∈ U, f s x ≠ g s x) :
    (∀ x ∈ U, f t x ≤ g t x) ∨ (∀ x ∈ U, g t x ≤ f t x) := by
  by_contra! h
  obtain ⟨⟨b,hb,eb⟩,a,ha,ea⟩ := h
  have small := (hf a ha).eventually_lt (hg a ha) ea
  have big := (hg b hb).eventually_lt (hf b hb) eb
  obtain ⟨s,⟨cf,cg,dis⟩,l,r⟩ := (hsep.and_eventually (small.and big)).exists
  obtain ⟨x,hx,same⟩ := hU.intermediate_value₂ ha hb cf cg l.le r.le
  exact dis x hx same

/-- Local coordinates of a family of surface sheets over the horizontal
plane. The inverse chart keeps the deformation parameter fixed. -/
theorem parameterized_sheet_inverse_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ × E → E) {t : ℝ} {u : E} (hc : ContDiffAt ℝ 1 H (t,u))
    (hD : Function.Bijective (fderiv ℝ (fun w : E => H (t,w)) u)) :
    ∃ (V : Set (ℝ × E)) (p : ℝ × E → E), IsOpen V ∧ (t,H (t,u)) ∈ V ∧
      ContinuousOn p V ∧ p (t,H (t,u))=u ∧ ∀ q ∈ V, H (q.1,p q)=q.2 := by
  let D := fderiv ℝ H (t,u)
  let G := fun q : ℝ × E => (q.1,H q)
  let J := (ContinuousLinearMap.fst ℝ ℝ E).prod D
  have hJ : HasStrictFDerivAt G J (t,u) := (ContinuousLinearMap.fst ℝ ℝ E).hasStrictFDerivAt.prodMk (hc.hasStrictFDerivAt one_ne_zero)
  have hfix : HasFDerivAt (fun w : E => (t,w)) ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) u :=
    (hasFDerivAt_const t u).prodMk (hasFDerivAt_id u)
  have fixedDeriv (v : E) : (fderiv ℝ (fun w : E => H (t,w)) u) v = D (0,v) :=
    congrArg (fun d : E →L[ℝ] E => d v) ((hc.differentiableAt one_ne_zero).hasFDerivAt.comp u hfix).fderiv
  have add (s : ℝ) (v : E) : D (s,v) = D (s,0)+D (0,v) := by
    rw [← map_add]; simp
  have inj : Function.Injective J := by
    rintro ⟨s,x⟩ ⟨v,y⟩ same
    have e : s=v := congrArg Prod.fst same
    subst v
    have f : D (s,x) = D (s,y) := congrArg Prod.snd same
    rw [add s x,add s y] at f
    exact Prod.ext rfl (hD.1 (by rw [fixedDeriv,fixedDeriv]; exact add_left_cancel f))
  have surj : Function.Surjective J := by
    rintro ⟨s,v⟩
    obtain ⟨x,hx⟩ := hD.2 (v-D (s,0))
    refine ⟨(s,x),Prod.ext rfl ?_⟩
    change D (s,x) = v
    rw [add,← fixedDeriv,hx,add_sub_cancel]
  let e := ContinuousLinearEquiv.ofBijective J (LinearMap.ker_eq_bot.mpr inj) (LinearMap.range_eq_top.mpr surj)
  have he : HasStrictFDerivAt G e.toContinuousLinearMap (t,u) := hJ
  let K := he.toOpenPartialHomeomorph G
  have hu : (t,u) ∈ K.source := he.mem_toOpenPartialHomeomorph_source
  have center : (t,H (t,u)) ∈ K.target := K.map_source hu
  refine ⟨K.target,fun q => (K.symm q).2,K.open_target,center,continuous_snd.comp_continuousOn K.continuousOn_symm,?_,?_⟩
  · exact congrArg Prod.snd (K.left_inv hu)
  · intro q hq
    have ee : ((K.symm q).1,H (K.symm q)) = q := K.right_inv hq
    rw [← congrArg Prod.fst ee]
    exact congrArg Prod.snd ee

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_sheets_ordered_at_first_contact
#print axioms TwoAxisHelicoid.parameterized_sheet_inverse_chart
