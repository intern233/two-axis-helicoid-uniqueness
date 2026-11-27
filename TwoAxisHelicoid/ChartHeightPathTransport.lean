import Mathlib.Topology.UnitInterval
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology unitInterval

/-- Move an arbitrary compact set of a height fiber inside its chart,
interpolating the horizontal displacement at two marked points. -/
theorem compact_height_chart_transport {M S T : Type*} [TopologicalSpace M] [TopologicalSpace S]
    [TopologicalSpace T] [CompactSpace T] {t₀ t₁ : T} (blend : C(T,ℝ)) (b₀ : blend t₀=0) (b₁ : blend t₁=1)
    {h : M → ℝ} (e : OpenPartialHomeomorph M (ℝ×ℝ))
    (height : ∀ w∈e.target, h (e.symm w)=w.2)
    (γ : C(T,M)) (inside : ∀ t, γ t∈e.source) {c : ℝ} (level : ∀ t, h (γ t)=c)
    (v L R : C(S,ℝ)) {s₀ : S} (atHeight : v s₀=c)
    (start : L s₀=(e (γ t₀)).1) (finish : R s₀=(e (γ t₁)).1) :
    ∃ V : Set S, IsOpen V ∧ s₀∈V ∧ ∃ F : S×T → M,
      ContinuousOn F (V ×ˢ univ) ∧ (∀ t, F (s₀,t)=γ t) ∧
      ∀ s∈V, (∀ t, F (s,t)∈e.source ∧ h (F (s,t))=v s) ∧
        F (s,t₀)=e.symm (L s,v s) ∧ F (s,t₁)=e.symm (R s,v s) := by
  let u := fun t : T => (e (γ t)).1
  have cu : Continuous u := continuous_iff_continuousAt.mpr (fun t =>
    ((e.continuousAt (inside t)).fst).comp γ.continuous.continuousAt)
  let A := fun q : S×T =>
    (u q.2+(1-blend q.2)*(L q.1-u t₀)+blend q.2*(R q.1-u t₁),v q.1)
  have cont : Continuous A := by
    dsimp only [A]
    fun_prop
  have atBase (t : T) : A (s₀,t)=e (γ t) := by
    have yh := height (e (γ t)) (e.map_source (inside t))
    rw [e.left_inv (inside t),level t] at yh
    apply Prod.ext
    · simp only [A,u,start,finish,sub_self,mul_zero,add_zero]
    · exact atHeight.trans yh
  have everywhere : ∀ᶠ s in 𝓝 s₀, ∀ t∈(univ : Set T), A (s,t)∈e.target := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro t _
    exact cont.continuousAt.eventually (e.open_target.mem_nhds (by rw [atBase]; exact e.map_source (inside t)))
  obtain ⟨V,subset,op,mem⟩ := mem_nhds_iff.mp everywhere
  refine ⟨V,op,mem,e.symm ∘ A,e.continuousOn_symm.comp cont.continuousOn (fun q hq => subset hq.1 q.2 trivial),?_,?_⟩
  · intro t
    exact (congrArg e.symm (atBase t)).trans (e.left_inv (inside t))
  · intro s hs
    refine ⟨fun t => ⟨e.map_target (subset hs t trivial),height _ (subset hs t trivial)⟩,?_,?_⟩
    · change e.symm (A (s,t₀))=_
      apply congrArg e.symm
      apply Prod.ext
      · change u t₀+(1-blend t₀)*(L s-u t₀)+blend t₀*(R s-u t₁)=L s
        rw [b₀]
        ring
      · rfl
    · change e.symm (A (s,t₁))=_
      apply congrArg e.symm
      apply Prod.ext
      · change u t₁+(1-blend t₁)*(L s-u t₀)+blend t₁*(R s-u t₁)=R s
        rw [b₁]
        ring
      · rfl

/-- Transport a compact regular height path in a product chart, with the
two endpoints allowed to move independently on the adjoining height
fibers. The transport starts at the prescribed path itself. -/
theorem chart_transport_regular_height_path {M S : Type*} [TopologicalSpace M] [TopologicalSpace S]
    {h : M → ℝ} (e : OpenPartialHomeomorph M (ℝ×ℝ))
    (height : ∀ w∈e.target, h (e.symm w)=w.2)
    (γ : C(I,M)) (inside : ∀ t, γ t∈e.source) {c : ℝ} (level : ∀ t, h (γ t)=c)
    (v L R : C(S,ℝ)) {s₀ : S} (atHeight : v s₀=c)
    (start : L s₀=(e (γ 0)).1) (finish : R s₀=(e (γ 1)).1) :
    ∃ V : Set S, IsOpen V ∧ s₀∈V ∧ ∃ F : S×I → M,
      ContinuousOn F (V ×ˢ univ) ∧ (∀ t, F (s₀,t)=γ t) ∧
      ∀ s∈V, (∀ t, F (s,t)∈e.source ∧ h (F (s,t))=v s) ∧
        F (s,0)=e.symm (L s,v s) ∧ F (s,1)=e.symm (R s,v s) :=
  compact_height_chart_transport (t₀:=(0:I)) (t₁:=(1:I)) ⟨Subtype.val,continuous_subtype_val⟩ rfl rfl
    e height γ inside level v L R atHeight start finish

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_height_chart_transport
#print axioms TwoAxisHelicoid.chart_transport_regular_height_path
