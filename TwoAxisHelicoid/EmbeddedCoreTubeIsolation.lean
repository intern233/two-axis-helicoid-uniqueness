import TwoAxisHelicoid.SpatialSheetImageConvergence
import TwoAxisHelicoid.CompactHeightSlabSheets

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology

/-- Shrinking an embedded tube around a compact core separates its
nonzero normal heights from the entire original closed surface,
including the part parametrized outside the tube base. -/
theorem closed_surface_tube_meets_only_zero {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    {X : B → E} (embed : IsClosedEmbedding X) {T : B × ℝ → E} (ct : Continuous T)
    (zero : ∀ b, T (b,0)=X b) {K U : Set B} (kc : IsCompact K) (uo : IsOpen U) (ku : K⊆U)
    {r : ℝ} (rp : 0<r) (tube : IsOpenEmbedding ((U ×ˢ ball (0:ℝ) r).domRestrict T)) :
    ∃ (V : Set B) (s : ℝ), IsOpen V ∧ K⊆V ∧ V⊆U ∧ 0<s ∧
      ∀ b∈V, ∀ h : ℝ, |h|<s → (T (b,h)∈range X ↔ h=0) := by
  let W := U ×ˢ ball (0:ℝ) r
  let away := X '' Uᶜ
  have ac : IsClosed away := embed.isClosedMap _ uo.isClosed_compl
  have op : IsOpen (W∩T ⁻¹' awayᶜ) := (uo.prod isOpen_ball).inter (ac.isOpen_compl.preimage ct)
  have contains : K ×ˢ ({0}:Set ℝ)⊆W∩T ⁻¹' awayᶜ := by
    rintro ⟨b,h⟩ ⟨hb,hh⟩
    change h=0 at hh
    subst h
    refine ⟨⟨ku hb,mem_ball_self rp⟩,?_⟩
    change T (b,0)∉away
    rw [zero]
    rintro ⟨y,hy,e⟩
    exact hy (by rw [embed.injective e]; exact ku hb)
  obtain ⟨V,I,vo,io,kv,zi,sub⟩ := generalized_tube_lemma kc isCompact_singleton op contains
  have iz : (0:ℝ)∈I := zi (mem_singleton _)
  obtain ⟨s,sp,si⟩ := Metric.mem_nhds_iff.mp (io.mem_nhds iz)
  have inside (b : B) (hb : b∈V) (h : ℝ) (hh : |h|<s) : (b,h)∈W∩T ⁻¹' awayᶜ :=
    sub ⟨hb,si (by simpa [mem_ball,Real.dist_eq] using hh)⟩
  have inj : InjOn T W := injOn_iff_injective.mpr tube.injective
  refine ⟨V,s,vo,kv,fun b hb => (sub (show (b,(0:ℝ))∈V ×ˢ I from ⟨hb,iz⟩)).1.1,sp,?_⟩
  intro b hb h hh
  have atH := inside b hb h hh
  constructor
  · rintro ⟨y,eq⟩
    have yu : y∈U := by
      by_contra yn
      exact atH.2 ⟨y,yn,eq⟩
    have eq' : (b,h)=(y,0) := inj atH.1 ⟨yu,mem_ball_self rp⟩ (eq.symm.trans (zero y).symm)
    exact congrArg Prod.snd eq'
  · rintro rfl
    exact ⟨b,(zero b).symm⟩

/-- Upper local convergence of the spatial images forces every sheet
over the fixed compact core to have uniformly small signed height.
Only sheets inside the chosen smaller tube are considered. -/
theorem convergent_closed_surfaces_core_heights {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    {S : ℕ → Set E} {X : B → E} (conv : LocalSpatialImageLimit S (range X))
    {T : B × ℝ → E} (ct : Continuous T) {K : Set B} (kc : IsCompact K) {r : ℝ}
    (isolate : ∀ b∈K, ∀ h : ℝ, |h|<r → T (b,h)∈range X → h=0)
    {R : ℝ} (inner : R<r) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ n in atTop, ∀ b∈K, ∀ h : ℝ, |h|≤R → T (b,h)∈S n → |h|<ε := by
  let I := Icc (-R) R ∩ {t : ℝ | ε≤|t|}
  have ic : IsCompact I := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have avoid : Disjoint (T '' (K ×ˢ I)) (range X) := by
    apply disjoint_left.mpr
    rintro y ⟨⟨b,h⟩,⟨hb,hi⟩,rfl⟩ mem
    have eq := isolate b hb h ((abs_le.mpr hi.1).trans_lt inner) mem
    have low : ε≤|h| := hi.2
    rw [eq,abs_zero] at low
    exact ep.not_ge low
  filter_upwards [conv.eventually_disjoint_compact ((kc.prod ic).image ct) avoid] with n hn
  intro b hb h bound member
  by_contra! large
  exact disjoint_left.mp hn member ⟨(b,h),⟨hb,abs_le.mp bound,large⟩,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.closed_surface_tube_meets_only_zero
#print axioms TwoAxisHelicoid.convergent_closed_surfaces_core_heights
