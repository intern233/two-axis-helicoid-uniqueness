import TwoAxisHelicoid.TorusSchwarzNormalization

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ComplexConjugate

/-- A closed embedded harmonic conformal punctured torus containing both
straight axes yields the actual normalized harmonic immersion used in the
integer-family reduction. No domain reflection or lattice shape is supplied. -/
theorem straight_axes_to_two_axis_harmonic_immersion (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hhor : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    ∃ (s : ℂ) (t : ℝ) (_ : s ≠ 0) (ht : 0 < t),
      (∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ (rhombicPeriodPair t ht).lattice) ∧
      TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht)
        (fun z => X (periodTorusProjection L (s⁻¹*z))) := by
  obtain ⟨s,t,hs,ht,hp,href⟩ := straight_axes_harmonic_torus_rhombic_reflections L X hX hhor hver hhi
  let M := rhombicPeriodPair t ht
  let e := periodTorusScalingHomeomorph L M s hs hp
  let Y := X ∘ periodTorusProjection L
  let u := fun z : ℂ => s⁻¹*z
  let Z := Y ∘ u
  have hzL {z : ℂ} (hz : z ∉ M.lattice) : u z ∉ L.lattice := by
    intro h
    exact hz (by simpa [u,← mul_assoc,hs] using (hp _).mp h)
  have hcoord (z : ℂ) (hz : z ∉ M.lattice) :
      (∀ j, HarmonicAt (fun w => Z w j) z) ∧ ConformalCoordinateDerivatives Z z ∧ Function.Injective (fderiv ℝ Z z) := by
    obtain ⟨hh,hc,hi⟩ := hhi _ (hzL hz)
    have hu : HasDerivAt u s⁻¹ z := by simpa [u] using (hasDerivAt_id z).const_mul s⁻¹
    exact harmonic_immersion_reparametrization hh hc hi (analyticAt_const.mul analyticAt_id)
      (hu.deriv.symm ▸ inv_ne_zero hs)
  have hx (z : ℂ) (hz : z ∉ M.lattice) : Z (conj z) = halfTurnX (Z z) :=
    (href (periodTorusProjection M z) (fun h => hz ((periodTorusProjection_eq_zero M _).mp h))).1
  have hv (z : ℂ) (hz : z ∉ M.lattice) : Z (-conj z) = halfTurnZ (Z z) :=
    (href (periodTorusProjection M z) (fun h => hz ((periodTorusProjection_eq_zero M _).mp h))).2
  refine ⟨s,t,hs,ht,hp,?_⟩
  refine ⟨fun z hz => (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((hcoord z hz).1 j))).differentiableAt,
    fun z hz => (hcoord z hz).1,fun z hz => (hcoord z hz).2.1,fun z hz => (hcoord z hz).2.2,?_,?_,hx⟩
  · intro z _ ω hω
    change X (e.symm (periodTorusProjection M (z+ω))) = X (e.symm (periodTorusProjection M z))
    rw [periodTorusProjection_add_lattice M _ _ hω]
  · intro z hz
    have hn : conj z ∉ M.lattice := fun h => hz (by
      have := rhombic_conj_mem ht h
      simpa using this)
    have he := hv (conj z) hn
    rw [starRingEnd_self_apply,hx z hz] at he
    exact he.trans (by ext j; fin_cases j <;> simp [halfTurnX,halfTurnZ,Z,Y,u])

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.straight_axes_to_two_axis_harmonic_immersion
