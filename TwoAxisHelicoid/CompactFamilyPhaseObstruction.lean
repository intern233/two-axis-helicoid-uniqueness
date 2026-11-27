import TwoAxisHelicoid.CircleLiftNeighborhood
import Mathlib.Topology.Compactness.Compact

namespace TwoAxisHelicoid
open Set Filter Topology Complex
open scoped Topology

/-- A phase lift on a sufficiently close member of a continuous
compact family gives a lift on its base member. The correction is the
single-valued argument of the pointwise quotient in the right half-plane. -/
theorem compact_family_phase_at_base {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [CompactSpace T] (f : C(S×T,Circle)) (s₀ : S) :
    ∀ᶠ s in 𝓝 s₀, (∃ u : C(T,ℝ), ∀ t, normalizedPhase (u t)=f (s,t)) →
      ∃ u : C(T,ℝ), ∀ t, normalizedPhase (u t)=f (s₀,t) := by
  let ratio := fun q : S×T => f (s₀,q.2)/f q
  have cr : Continuous ratio := (f.continuous.comp (continuous_const.prodMk continuous_snd)).div' f.continuous
  have cv : Continuous (fun q => ((ratio q:Circle):ℂ)) := continuous_subtype_val.comp cr
  have pos : ∀ᶠ s in 𝓝 s₀, ∀ t∈(univ : Set T), 0<((ratio (s,t):Circle):ℂ).re := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro t _
    apply (continuous_re.comp cv).continuousAt.eventually
    apply Ioi_mem_nhds
    simp [ratio]
  filter_upwards [pos] with s inside
  rintro ⟨u,rep⟩
  let corr := fun t : T => ((ratio (s,t):Circle):ℂ).arg/(2*Real.pi)
  have c : Continuous corr := by
    apply Continuous.div_const
    apply continuous_iff_continuousAt.mpr
    intro t
    have slit : ((ratio (s,t):Circle):ℂ)∈Complex.slitPlane := Or.inl (inside t trivial)
    exact (Complex.continuousAt_arg slit).comp (f:=fun z : T => ((ratio (s,z):Circle):ℂ)) (x:=t)
      (cv.comp (Continuous.prodMk_right s)).continuousAt
  refine ⟨⟨fun t => u t+corr t,u.continuous.add c⟩,?_⟩
  intro t
  change Circle.exp (2*Real.pi*(u t+corr t))=f (s₀,t)
  have cancel : 2*Real.pi*corr t=((ratio (s,t):Circle):ℂ).arg := by
    dsimp only [corr]
    field_simp
  rw [mul_add,Circle.exp_add,cancel,Circle.exp_arg]
  change normalizedPhase (u t)*(f (s₀,t)/f (s,t))=f (s₀,t)
  rw [rep]
  simp

/-- If a compact connected family member in one height fiber detects a
marked phase obstruction, the containing connected components in all
nearby fibers detect the same obstruction. This allows the singular
member to be replaced by an actual regular section after smoothing. -/
theorem nearby_height_component_nonlifting {S T M : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [CompactSpace T] [PreconnectedSpace T] [TopologicalSpace M]
    (F : C(S×T,M)) (H : C(M,Circle×Circle)) {h : M → ℝ} {v : S → ℝ}
    (height : ∀ s t, h (F (s,t))=v s) (s₀ : S) (t₀ : T)
    (obstruct : ¬∃ u w : C(T,ℝ), ∀ t, normalizedPhase (u t)=(H (F (s₀,t))).1 ∧
      normalizedPhase (w t)=(H (F (s₀,t))).2) :
    ∀ᶠ s in 𝓝 s₀, ∃ x : h ⁻¹' {v s}, ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2 := by
  let u : C(S×T,Circle) := ⟨fun q => (H (F q)).1, (H.continuous.comp F.continuous).fst⟩
  let w : C(S×T,Circle) := ⟨fun q => (H (F q)).2, (H.continuous.comp F.continuous).snd⟩
  filter_upwards [compact_family_phase_at_base u s₀,compact_family_phase_at_base w s₀] with s first second
  let g := fun t : T => (⟨F (s,t),height s t⟩ : h ⁻¹' {v s})
  have cg : Continuous g := (F.continuous.comp (Continuous.prodMk_right s)).subtype_mk _
  have inside : range g⊆connectedComponent (g t₀) :=
    (isPreconnected_range cg).subset_connectedComponent (mem_range_self t₀)
  let G : C(T,connectedComponent (g t₀)) := ⟨fun t => ⟨g t,inside (mem_range_self t)⟩,cg.subtype_mk _⟩
  refine ⟨g t₀,?_⟩
  rintro ⟨a,b,rep⟩
  obtain ⟨A,ra⟩ := first ⟨a.comp G,fun t => (rep (G t)).1⟩
  obtain ⟨B,rb⟩ := second ⟨b.comp G,fun t => (rep (G t)).2⟩
  exact obstruct ⟨A,B,fun t => ⟨ra t,rb t⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_family_phase_at_base
#print axioms TwoAxisHelicoid.nearby_height_component_nonlifting
