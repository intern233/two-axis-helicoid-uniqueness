import TwoAxisHelicoid.TorusVerticalSchwarzSymmetry
import TwoAxisHelicoid.HarmonicImmersionReparametrization
import TwoAxisHelicoid.HarmonicNullLift

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ComplexConjugate

/-- The two ambient straight lines determine the normalized rhombic quotient
reflections of the actual surface. -/
theorem straight_axes_harmonic_torus_rhombic_reflections (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hhor : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    ∃ (s : ℂ) (t : ℝ) (hs : s ≠ 0) (ht : 0 < t)
      (hp : ∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ (rhombicPeriodPair t ht).lattice),
      let e := periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp
      ∀ q : PeriodTorus (rhombicPeriodPair t ht), q ≠ 0 →
        X (e.symm (rhombicHorizontalReflection ht q)) = halfTurnX (X (e.symm q)) ∧
        X (e.symm (rhombicVerticalReflection ht q)) = halfTurnZ (X (e.symm q)) := by
  obtain ⟨f,hf,he⟩ := closed_embedded_torus_horizontal_schwarz L X hX hhor hhi
  obtain ⟨g,hg,hgE⟩ := closed_embedded_torus_vertical_schwarz L X hX hver hhi
  let F := compactPunctureExtension f
  let G := compactPunctureExtension g
  have hF (q : PeriodTorus L) (hq : q ≠ 0) : X (F q) = halfTurnX (X q) :=
    (congrArg X (compactPunctureExtension_apply f ⟨q,hq⟩)).trans (he ⟨q,hq⟩)
  have hG (q : PeriodTorus L) (hq : q ≠ 0) : X (G q) = halfTurnZ (X q) :=
    (congrArg X (compactPunctureExtension_apply g ⟨q,hq⟩)).trans (hgE ⟨q,hq⟩)
  have hcon : ContinuousOn X {q | q ≠ 0} := continuousOn_iff_continuous_domRestrict.mpr hX.continuous
  obtain ⟨s,t,hs,ht,hp,hfe,hge⟩ := embedded_torus_axes_rhombic_normalization L
    (fun q hq => (hcon q hq).continuousAt (isOpen_ne.mem_nhds hq)) hX.isEmbedding hhor
    F G (punctured_torus_anti_extension L L f hf) (punctured_torus_anti_extension L L g hg)
    (compactPunctureExtension_at_end f) (compactPunctureExtension_at_end g) hF hG
  refine ⟨s,t,hs,ht,hp,?_⟩
  let e := periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp
  have he0 : e 0 = 0 := by
    change periodTorusProjection _ (s*0) = 0
    simp
  intro _ q hq
  have hqn : e.symm q ≠ 0 := fun h => hq ((e.apply_symm_apply q).symm.trans ((congrArg e h).trans he0))
  have hf' := hfe (e.symm q)
  have hg' := hge (e.symm q)
  change e (F (e.symm q)) = rhombicHorizontalReflection ht (e (e.symm q)) at hf'
  change e (G (e.symm q)) = rhombicVerticalReflection ht (e (e.symm q)) at hg'
  rw [e.apply_symm_apply] at hf' hg'
  exact ⟨(congrArg X (e.symm_apply_eq.mpr hf'.symm)).trans (hF _ hqn),
    (congrArg X (e.symm_apply_eq.mpr hg'.symm)).trans (hG _ hqn)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.straight_axes_harmonic_torus_rhombic_reflections
