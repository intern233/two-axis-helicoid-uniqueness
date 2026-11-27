import TwoAxisHelicoid.TorusAntiholomorphicPuncture
import TwoAxisHelicoid.EmbeddedRangeInvolution
import TwoAxisHelicoid.EmbeddedTorusAxesNormalization

namespace TwoAxisHelicoid
open Complex Set Topology

theorem halfTurnX_continuous : Continuous halfTurnX := by
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp [halfTurnX] <;> fun_prop

theorem halfTurnZ_continuous : Continuous halfTurnZ := by
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp [halfTurnZ] <;> fun_prop

/-- The rhombic normalization can start on the punctured domain itself.
The actual ambient symmetries determine its homeomorphisms by embedding,
and their anti-holomorphic local coordinates force the compact extensions. -/
theorem embedded_punctured_axes_rhombic_normalization (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ}
    (hX : ∀ q ≠ 0, ContinuousAt X q)
    (hEmb : IsEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (haxis : ∀ r : ℝ, ∃ q : PuncturedPeriodTorus L, X q.1 = ![r,0,0])
    (hhor : ∀ q : PuncturedPeriodTorus L, halfTurnX (X q.1) ∈ range (fun p : PuncturedPeriodTorus L => X p.1))
    (hver : ∀ q : PuncturedPeriodTorus L, halfTurnZ (X q.1) ∈ range (fun p : PuncturedPeriodTorus L => X p.1))
    (hf : PuncturedTorusAntiholomorphic L L
      (embeddedRangeInvolution hEmb halfTurnX halfTurnX_continuous halfTurnX_involutive hhor))
    (hg : PuncturedTorusAntiholomorphic L L
      (embeddedRangeInvolution hEmb halfTurnZ halfTurnZ_continuous halfTurnZ_involutive hver)) :
    ∃ (s : ℂ) (t : ℝ) (hs : s ≠ 0) (ht : 0 < t)
      (hp : ∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ (rhombicPeriodPair t ht).lattice),
      let e := periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp
      let f := embeddedRangeInvolution hEmb halfTurnX halfTurnX_continuous halfTurnX_involutive hhor
      let g := embeddedRangeInvolution hEmb halfTurnZ halfTurnZ_continuous halfTurnZ_involutive hver
      (∀ q : PuncturedPeriodTorus L, e (f q).1 = rhombicHorizontalReflection ht (e q.1)) ∧
      (∀ q : PuncturedPeriodTorus L, e (g q).1 = rhombicVerticalReflection ht (e q.1)) := by
  let f := embeddedRangeInvolution hEmb halfTurnX halfTurnX_continuous halfTurnX_involutive hhor
  let g := embeddedRangeInvolution hEmb halfTurnZ halfTurnZ_continuous halfTurnZ_involutive hver
  have heqf (q : PeriodTorus L) (hq : q ≠ 0) : X (compactPunctureExtension f q) = halfTurnX (X q) := by
    rw [compactPunctureExtension_apply f (⟨q,hq⟩ : PuncturedPeriodTorus L)]
    exact embeddedRangeInvolution_eq hEmb _ _ _ hhor _
  have heqg (q : PeriodTorus L) (hq : q ≠ 0) : X (compactPunctureExtension g q) = halfTurnZ (X q) := by
    rw [compactPunctureExtension_apply g (⟨q,hq⟩ : PuncturedPeriodTorus L)]
    exact embeddedRangeInvolution_eq hEmb _ _ _ hver _
  obtain ⟨s,t,hs,ht,hp,hf',hg'⟩ := embedded_torus_axes_rhombic_normalization L hX hEmb haxis
    (compactPunctureExtension f) (compactPunctureExtension g)
    (punctured_torus_anti_extension L L f hf) (punctured_torus_anti_extension L L g hg)
    (compactPunctureExtension_at_end f) (compactPunctureExtension_at_end g) heqf heqg
  refine ⟨s,t,hs,ht,hp,fun q => ?_,fun q => ?_⟩
  · simpa only [compactPunctureExtension_apply] using hf' q.1
  · simpa only [compactPunctureExtension_apply] using hg' q.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_punctured_axes_rhombic_normalization
