import TwoAxisHelicoid.EmbeddedCoreTubeIsolation

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology

/-- Restrict an embedded tube to any smaller open base and height
interval. Its physical image is still open in ambient space. -/
theorem open_subtube_image {B E : Type*} [TopologicalSpace B] [TopologicalSpace E] {U V : Set B}
    {T : B × ℝ → E} {r s : ℝ} (tube : IsOpenEmbedding ((U ×ˢ ball (0:ℝ) r).domRestrict T))
    (sub : V⊆U) (vo : IsOpen V) (small : s≤r) : IsOpen (T '' (V ×ˢ ball (0:ℝ) s)) := by
  let W := U ×ˢ ball (0:ℝ) r
  let A := V ×ˢ ball (0:ℝ) s
  have inside : A⊆W := prod_mono sub (ball_subset_ball small)
  have eq : (W.domRestrict T) '' (Subtype.val ⁻¹' A)=T '' A := by
    ext y
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q.1,hq,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨q,inside hq⟩,hq,rfl⟩
  exact eq ▸ tube.isOpenMap _ ((vo.prod isOpen_ball).preimage continuous_subtype_val)

/-- On an open connected core with compact closure, local convergence
of the physical surfaces alone forces every inner tube to be met and
every sheet there to have small height. Whenever its projection is
transverse, it is proper and onto the entire core and its local sheets
are exhaustive and finite. -/
theorem convergent_embedded_core_tube_exhaustion {B E : Type*} [TopologicalSpace B] [T2Space B] [TopologicalSpace E]
    {X : B → E} (embed : IsClosedEmbedding X) {T : B × ℝ → E} (ct : Continuous T)
    (zero : ∀ b, T (b,0)=X b) {V : Set B} (vo : IsOpen V) (vn : V.Nonempty) [PreconnectedSpace V]
    (kc : IsCompact (closure V)) {U : Set B} (uo : IsOpen U) (ku : closure V⊆U) {r : ℝ} (rp : 0<r)
    (tube : IsOpenEmbedding ((U ×ˢ ball (0:ℝ) r).domRestrict T))
    {S : ℕ → Set E} (closed : ∀ n, IsClosed (S n)) (conv : LocalSpatialImageLimit S (range X)) :
    let TV := fun q : V × ℝ => T (q.1.1,q.2)
    ∃ R : ℝ, 0<R ∧ R<r ∧
      (∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, ∀ q∈spatialTubeSlice TV (S n) R, |q.2|<ε) ∧
      ∀ᶠ n in atTop, (spatialTubeSlice TV (S n) R).Nonempty ∧
        let p := fun q : spatialTubeSlice TV (S n) R => q.1.1
        IsProperMap p ∧ (IsLocalHomeomorph p → Function.Surjective p ∧ ∀ b : V, Nonempty (FiniteSheetGerms p b)) := by
  let TV := fun q : V × ℝ => T (q.1.1,q.2)
  have ctv : Continuous TV := ct.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨W,s,_,kw,_,sp,iso⟩ := closed_surface_tube_meets_only_zero embed ct zero kc uo ku rp tube
  let R := min s r/2
  have pos : 0<R := half_pos (lt_min sp rp)
  have ls : R<s := (half_lt_self (lt_min sp rp)).trans_le (min_le_left _ _)
  have lr : R<r := (half_lt_self (lt_min sp rp)).trans_le (min_le_right _ _)
  have bound (ε : ℝ) (ep : 0<ε) : ∀ᶠ n in atTop, ∀ q∈spatialTubeSlice TV (S n) R, |q.2|<ε := by
    filter_upwards [convergent_closed_surfaces_core_heights conv ct kc
      (fun b hb h hh im => (iso b (kw hb) h hh).mp im) ls ep] with n hn
    intro q hq
    exact hn q.1.1 (subset_closure q.1.2) q.2 hq.1.le hq.2
  let P := T '' (V ×ˢ ball (0:ℝ) R)
  have op : IsOpen P := open_subtube_image tube (fun b hb => ku (subset_closure hb)) vo lr.le
  obtain ⟨b,hb⟩ := vn
  have hit : X b∈P := ⟨(b,0),⟨hb,mem_ball_self pos⟩,zero b⟩
  have eventuallyHit := conv.1 (X b) (mem_range_self b) P (op.mem_nhds hit)
  refine ⟨R,pos,lr,bound,?_⟩
  filter_upwards [eventuallyHit,bound (R/2) (half_pos pos)] with n meets thin
  obtain ⟨y,hy,⟨q,hq,rfl⟩⟩ := meets
  have somePoint : (spatialTubeSlice TV (S n) R).Nonempty :=
    ⟨(⟨q.1,hq.1⟩,q.2),by simpa only [mem_ball,Real.dist_eq,sub_zero] using hq.2,hy⟩
  let _ : Nonempty (spatialTubeSlice TV (S n) R) := somePoint.to_subtype
  have proper := compact_height_slab_projection_proper ctv (closed n) (half_lt_self pos) (fun z hz => (thin z hz).le)
  refine ⟨somePoint,proper,fun loc => ?_⟩
  have sur := proper_local_homeomorph_surjective proper loc
  exact ⟨sur,finite_sheet_germs_of_proper_projection proper loc sur⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.convergent_embedded_core_tube_exhaustion
