import TwoAxisHelicoid.CertifiedCompactDoublePoints

namespace TwoAxisHelicoid
open Set Topology

/-- A compact set of distinct parameter pairs stays a positive uniform
distance away from the diagonal, even on a noncompact parameter surface. -/
theorem compact_pairs_away_from_diagonal {M : Type*} [MetricSpace M] {D : Set (M × M)}
    (hD : IsCompact D) (hne : ∀ p ∈ D, p.1 ≠ p.2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ D, δ ≤ dist p.1 p.2 := by
  by_cases h : D.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hD.exists_isMinOn h (continuous_fst.dist continuous_snd).continuousOn
    exact ⟨dist p.1 p.2,dist_pos.mpr (hne p hp),fun q hq => hmin hq⟩
  · exact ⟨1,one_pos,fun p hp => (h ⟨p,hp⟩).elim⟩

/-- A positive distance from the diagonal reduces injectivity to an
ambient separation bound on a compact set of parameter pairs. -/
theorem compact_core_separation_test {M E : Type*} [MetricSpace M] [MetricSpace E]
    (F : M → E) (hF : Continuous F) (K : Set M) (hK : IsCompact K)
    (hD : IsCompact (immersionDoublePoints F)) (hs : immersionDoublePoints F ⊆ K ×ˢ K)
    (hE : IsClosedEmbedding F ↔ InjOn F K) :
    ∃ (K : Set M) (δ : ℝ), IsCompact K ∧ 0 < δ ∧
      (∀ x y, F x = F y → x ≠ y → x ∈ K ∧ y ∈ K ∧ δ ≤ dist x y) ∧
      (IsClosedEmbedding F ↔ ∃ ε : ℝ, 0 < ε ∧
        ∀ x ∈ K, ∀ y ∈ K, δ ≤ dist x y → ε ≤ dist (F x) (F y)) := by
  obtain ⟨δ,hδ,hgap⟩ := compact_pairs_away_from_diagonal hD (fun p hp => hp.2)
  have located (x y : M) (he : F x = F y) (hn : x ≠ y) : x ∈ K ∧ y ∈ K ∧ δ ≤ dist x y := by
    have h : (x,y) ∈ immersionDoublePoints F := ⟨he,hn⟩
    exact ⟨(hs h).1,(hs h).2,hgap _ h⟩
  refine ⟨K,δ,hK,hδ,located,?_,?_⟩
  · intro embedded
    let S := (K ×ˢ K) ∩ {p : M × M | δ ≤ dist p.1 p.2}
    have hS : IsCompact S := (hK.prod hK).inter_right (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
    by_cases hn : S.Nonempty
    · have hc : Continuous (fun p : M × M => dist (F p.1) (F p.2)) :=
        (hF.comp continuous_fst).dist (hF.comp continuous_snd)
      obtain ⟨p,hp,hmin⟩ := hS.exists_isMinOn hn hc.continuousOn
      have hne : F p.1 ≠ F p.2 := by
        intro he
        have hle : δ ≤ dist p.1 p.2 := hp.2
        rw [embedded.injective he,dist_self] at hle
        exact hδ.not_ge hle
      exact ⟨_,dist_pos.mpr hne,fun x hx y hy hxy => hmin (show (x,y) ∈ S from ⟨⟨hx,hy⟩,hxy⟩)⟩
    · exact ⟨1,one_pos,fun x hx y hy hxy => (hn ⟨(x,y),⟨hx,hy⟩,hxy⟩).elim⟩
  · rintro ⟨ε,hε,lower⟩
    apply hE.mpr
    intro x hx y hy eq
    by_contra hn
    have h := lower x hx y hy (located x y eq hn).2.2
    rw [eq,dist_self] at h
    exact hε.not_ge h

/-- The parameter distance is the certified immersion's intrinsic metric.
The second distance is in ambient Euclidean space. -/
theorem certified_positive_separation_embedding_test :
    let intrinsicDist := @dist _ certifiedTorusInducedMetricSpace.toPseudoMetricSpace.toDist
    let F := certifiedTorusImmersion
    ∃ (K : Set (PuncturedPeriodTorus certifiedPeriodPair)) (δ : ℝ), IsCompact K ∧ 0 < δ ∧
      (∀ x y, F x = F y → x ≠ y → x ∈ K ∧ y ∈ K ∧ δ ≤ intrinsicDist x y) ∧
      (IsClosedEmbedding F ↔ ∃ ε : ℝ, 0 < ε ∧
        ∀ x ∈ K, ∀ y ∈ K, δ ≤ intrinsicDist x y → ε ≤ dist (F x) (F y)) := by
  obtain ⟨hD,K,hK,hs,hE⟩ := certified_compact_embedding_criterion
  exact @compact_core_separation_test _ _ certifiedTorusInducedMetricSpace _ certifiedTorusImmersion certifiedTorusImmersion_continuous K hK hD hs hE

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_positive_separation_embedding_test
