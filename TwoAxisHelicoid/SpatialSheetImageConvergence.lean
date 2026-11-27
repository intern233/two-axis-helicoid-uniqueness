import TwoAxisHelicoid.SpatialImageCutoffCompactness
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology

/-- Local absence of the approximating surfaces implies their eventual
absence from any compact subset of the complement of the limit. -/
theorem LocalSpatialImageLimit.eventually_disjoint_compact {E : Type*} [TopologicalSpace E]
    {S : ℕ → Set E} {L K : Set E} (h : LocalSpatialImageLimit S L)
    (hk : IsCompact K) (hd : Disjoint K L) : ∀ᶠ n in atTop, Disjoint (S n) K := by
  classical
  have localAvoid (x : K) := h.2 x (fun hx => disjoint_left.mp hd x.2 hx)
  choose V hV hA using localAvoid
  obtain ⟨I,covers⟩ := hk.elim_nhds_subcover' (fun x hx => V ⟨x,hx⟩) (fun x hx => hV ⟨x,hx⟩)
  have finite : ∀ᶠ n : ℕ in atTop, ∀ x ∈ I, Disjoint (S n) (V x) := I.eventually_all.mpr (fun x _ => hA x)
  filter_upwards [finite] with n hn
  apply disjoint_left.mpr
  intro y hs hy
  obtain ⟨x,hu⟩ := mem_iUnion.mp (covers hy)
  obtain ⟨hx,hVx⟩ := mem_iUnion.mp hu
  exact disjoint_left.mp (hn x hx) hs hVx

/-- In a proper metric ambient space, upper and lower local convergence
of the geometric images gives pointwise convergence of distance to them.
No Hausdorff convergence at infinity is needed. -/
theorem LocalSpatialImageLimit.tendsto_infDist {E : Type*} [MetricSpace E] [ProperSpace E]
    {S : ℕ → Set E} {L : Set E} (h : LocalSpatialImageLimit S L) (hn : ∀ n, (S n).Nonempty)
    (hl : L.Nonempty) (x : E) : Tendsto (fun n => infDist x (S n)) atTop (𝓝 (infDist x L)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨b,hab,hb⟩ := exists_between ha
    have hd : Disjoint (closedBall x b) L := by
      apply disjoint_left.mpr
      intro y hy hL
      have d : dist x y ≤ b := (dist_comm y x) ▸ (mem_closedBall.mp hy)
      exact hb.not_ge ((infDist_le_dist_of_mem hL).trans d)
    filter_upwards [h.eventually_disjoint_compact (isCompact_closedBall x b) hd] with n H
    apply hab.trans_le ((le_infDist (hn n)).mpr ?_)
    intro y hy
    exact le_of_not_gt (fun e => disjoint_left.mp H hy (mem_closedBall.mpr (by simpa [dist_comm] using e.le)))
  · intro a ha
    obtain ⟨y,hy,hxy⟩ := (infDist_lt_iff hl).mp ha
    have nb : ball x a ∈ 𝓝 y := isOpen_ball.mem_nhds (by simpa [mem_ball,dist_comm] using hxy)
    filter_upwards [h.1 y hy (ball x a) nb] with n H
    obtain ⟨v,hv,hv'⟩ := H
    exact (infDist_le_dist_of_mem hv).trans_lt (by simpa [mem_ball,dist_comm] using hv')

/-- Compactly convergent geometric sheets identify the spatial images.
Every limit point is followed by a sheet, and the spatial graphs cover
every approximating point in the compact region. The sheet index may
depend on the surface number and no multiplicity is imposed. -/
theorem local_spatial_image_limit_of_sheet_positions {E : Type*} [MetricSpace E] [ProperSpace E]
    (S : ℕ → Set E) (L : Set E) (hclosed : IsClosed L) (hl : L.Nonempty)
    (lower : ∀ x ∈ L, ∃ p : ℕ → E, (∀ᶠ n in atTop, p n ∈ S n) ∧ Tendsto p atTop (𝓝 x))
    (charts : ∀ K : Set E, IsCompact K → ∃ (D : Type) (U : Set D) (F : ℕ → D → E) (g : D → E),
      MapsTo g U L ∧ TendstoUniformlyOn F g atTop U ∧ ∀ᶠ n in atTop, S n ∩ K ⊆ F n '' U) :
    LocalSpatialImageLimit S L := by
  refine ⟨?_,?_⟩
  · intro x hx V hV
    obtain ⟨p,hp,hlim⟩ := lower x hx
    filter_upwards [hp,hlim hV] with n hpn hn using ⟨p n,hpn,hn⟩
  · intro x hx
    let d := infDist x L
    have hd : 0 < d := (hclosed.notMem_iff_infDist_pos hl).mp hx
    obtain ⟨D,U,F,g,im,conv,coverage⟩ := charts (closedBall x (d/3)) (isCompact_closedBall x _)
    refine ⟨ball x (d/3),ball_mem_nhds _ (by positivity),?_⟩
    filter_upwards [coverage,Metric.tendstoUniformlyOn_iff.mp conv (d/3) (by positivity)] with n cover close
    apply disjoint_left.mpr
    intro y hy hxy
    obtain ⟨u,hu,rfl⟩ := cover ⟨hy,ball_subset_closedBall hxy⟩
    have h₁ : dist x (F n u) < d/3 := by simpa [mem_ball,dist_comm] using hxy
    have h₂ : dist (F n u) (g u) < d/3 := by simpa [dist_comm] using close u hu
    have h₃ : d ≤ dist x (g u) := infDist_le_dist_of_mem (im hu)
    linarith [dist_triangle x (F n u) (g u)]

/-- For compact cutoff families the underlying local sheet positions
suffice to transfer the published compactness statement to screw-period
exclusion. -/
theorem compact_screw_cutoffs_of_convergent_sheet_images {M : Type*} [TopologicalSpace M] [FirstCountableTopology M]
    (X : M → Set (Fin 3 → ℝ)) (hn : ∀ m, (X m).Nonempty) (hc : ∀ m, IsClosed (X m))
    (compact : ∀ η : ℝ, Real.pi/2 < η → IsCompact {m : M | HasNoScrewBelow η (X m)})
    (lower : ∀ (s : ℕ → M) m, Tendsto s atTop (𝓝 m) → ∀ x ∈ X m,
      ∃ p : ℕ → Fin 3 → ℝ, (∀ᶠ n in atTop, p n ∈ X (s n)) ∧ Tendsto p atTop (𝓝 x))
    (charts : ∀ (s : ℕ → M) m, Tendsto s atTop (𝓝 m) → ∀ K : Set (Fin 3 → ℝ), IsCompact K →
      ∃ (D : Type) (U : Set D) (F : ℕ → D → Fin 3 → ℝ) (g : D → Fin 3 → ℝ),
        MapsTo g U (X m) ∧ TendstoUniformlyOn F g atTop U ∧ ∀ᶠ n in atTop, X (s n) ∩ K ⊆ F n '' U) :
    CompactScrewCutoffs (range X) := by
  apply compact_screw_cutoffs_of_compact_families X hn hc compact
  intro s m h x
  exact (local_spatial_image_limit_of_sheet_positions _ _ (hc m) (hn m) (lower s m h) (charts s m h)).tendsto_infDist
    (fun n => hn (s n)) (hn m) x

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_screw_cutoffs_of_convergent_sheet_images
