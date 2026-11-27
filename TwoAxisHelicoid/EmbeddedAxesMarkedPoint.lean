import TwoAxisHelicoid.EmbeddedTorusAxesNormalization

namespace TwoAxisHelicoid
open Complex Set Topology

/-- The finite crossing of the two ambient axes is forced to be the nonzero
common fixed point of the normalized reflections. Thus the usual marking
E=0, O=1 is a conclusion of the actual embedding and normalization. -/
theorem embedded_axes_origin_normalizes_to_one (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ}
    (hEmb : IsEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (f g : PeriodTorus L ≃ₜ PeriodTorus L) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (heqf : ∀ q ≠ 0, X (f q) = halfTurnX (X q))
    (heqg : ∀ q ≠ 0, X (g q) = halfTurnZ (X q))
    {t : ℝ} (ht : 0 < t) (e : PeriodTorus L ≃ₜ PeriodTorus (rhombicPeriodPair t ht))
    (he0 : e 0 = 0)
    (hef : ∀ q, e (f q) = rhombicHorizontalReflection ht (e q))
    (heg : ∀ q, e (g q) = rhombicVerticalReflection ht (e q))
    {q : PeriodTorus L} (hq : q ≠ 0) (hXq : X q = 0) :
    e q = periodTorusProjection (rhombicPeriodPair t ht) 1 := by
  have hfixf : f q = q := by
    apply punctured_embedding_injective hEmb (homeomorph_puncture_ne f hf0 hq) hq
    rw [heqf q hq,hXq]
    ext j
    fin_cases j <;> simp [halfTurnX]
  have hfixg : g q = q := by
    apply punctured_embedding_injective hEmb (homeomorph_puncture_ne g hg0 hq) hq
    rw [heqg q hq,hXq]
    ext j
    fin_cases j <;> simp [halfTurnZ]
  have heq : rhombicHorizontalReflection ht (e q) = e q ∧
      rhombicVerticalReflection ht (e q) = e q := by
    rw [← hef q,← heg q,hfixf,hfixg]
    exact ⟨rfl,rfl⟩
  rcases (rhombic_reflections_common_fixed_points ht (e q)).mp heq with hzero | hone
  · exact False.elim (hq (e.injective (hzero.trans he0.symm)))
  · exact hone

theorem normalized_axes_origin_unique {t : ℝ} (ht : 0 < t)
    {X : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ}
    (hEmb : IsEmbedding (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => X q.1))
    (h0 : X (periodTorusProjection (rhombicPeriodPair t ht) 1) = 0) :
    ∀ q ≠ 0, X q = 0 ↔ q = periodTorusProjection (rhombicPeriodPair t ht) 1 := by
  intro q hq
  constructor
  · intro h
    exact punctured_embedding_injective hEmb hq (rhombic_common_fixed_points_distinct ht) (h.trans h0.symm)
  · intro h
    simpa [h] using h0

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_axes_origin_normalizes_to_one
