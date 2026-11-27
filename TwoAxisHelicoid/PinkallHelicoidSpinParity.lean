import TwoAxisHelicoid.StandardBoundaryMarkedParity
import TwoAxisHelicoid.SmoothRegularHomotopyCap
import TwoAxisHelicoid.HelicoidalTorusSpinParity
import TwoAxisHelicoid.EmbeddedIntegerFullSpinCap

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold

/-- The genus-one specialization of Pinkall, Topology (1985), Theorem 6.
The terminal embedding has the image of the standard torus and an
arbitrary marking. The homotopy is smooth on the closed time interval
and each slice is an immersion in the actual compact-surface atlas. -/
def PinkallEmbeddedTorusRegularHomotopy : Prop :=
  ∀ (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L)),
    let _ := cs
    IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) → IsClosedEmbedding F →
    ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F →
    (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p)) →
    ∃ H : ℝ × PeriodTorus L → Fin 3 → ℝ,
      (∀ p, H (0,p) = F p) ∧ IsEmbedding (fun p => H (1,p)) ∧
      range standardRoundTorusParameter = range (fun p => H (1,p)) ∧
      ContMDiffOn (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ × ℝ)) 𝓘(ℝ,Fin 3 → ℝ) ∞ H (Icc (0:ℝ) 1 ×ˢ univ) ∧
      (∀ (s : unitInterval) q, ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (fun p => H (s.1,p)) q) ∧
      ∀ (s : unitInterval) q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) (fun p => H (s.1,p)) q)

/-- The actual lift test on a compact cap follows from ordinary unmarked
regular homotopy to a standard round torus. The spatial disk, signs and
the unchanged genus-one Arf value are obtained without an Arf hypothesis. -/
theorem pinkall_even_on_punctured_marking (hPinkall : PinkallEmbeddedTorusRegularHomotopy)
    (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L)) :
    let _ := cs
    IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) → IsClosedEmbedding F →
    ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F →
    (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p)) →
    (∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus L)) q ∧
      ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus L)) q) →
    capAmbientSpinQuadratic L F (1,0) * capAmbientSpinQuadratic L F (0,1) = 0 := by
  intro inst hm he hF hFi hA
  obtain ⟨H,h0,h1,ht,hH,hs,hi⟩ := hPinkall L F cs hm he hF hFi
  have hr (p : PeriodTorus L) (hp : p ≠ 0) := cap_smooth_map_marked_regular L (cs := cs) (fun q => H (1,q))
    (hs 1 p) (hi 1 p) (hA p hp).1 (hA p hp).2
  have hend := standard_round_torus_all_markings_even L h1 ht (fun q hq => (hr q hq).1) (fun q hq => (hr q hq).2)
  have h := compact_regular_homotopy_even_arf L (cs := cs) H hH hs hi hA hend
  simpa only [funext h0] using h

theorem helicoidal_torus_marked_arf_zero_of_pinkall
    (hPinkall : PinkallEmbeddedTorusRegularHomotopy) (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ}
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hX : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (hsm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (hi : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    ∀ v w, torusIntersectionModTwo v w = 1 →
      capAmbientSpinQuadratic L X v * capAmbientSpinQuadratic L X w = 0 := by
  obtain ⟨F,cs,U,hm,he,hcap,hfi,hU,hpU,hCU,hfx,hcompat⟩ :=
    smooth_marked_helicoid_cap L A hA hAi hEnd hX hXi hsm hi (puncturedGeneratorCore_isCompact L)
  have hzero := pinkall_even_on_punctured_marking hPinkall L F cs hm he hcap hfi (fun p hp => (hcompat p hp).2.2)
  have hq : capAmbientSpinQuadratic L F = capAmbientSpinQuadratic L X := by
    classical
    unfold capAmbientSpinQuadratic
    simp only [cap_ambient_spin_closes_of_eq_near_generators L hU hCU hfx]
  intro v w hvw
  rw [cap_ambient_arf_basis L X v w hvw, ← hq]
  exact hzero

variable {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : (C : ℂ)^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)

include ht ha hc m hC0 hC hX hp hh hg in
/-- Application of the single published geometric input to the cap of an
embedded branch. All its manifold, marking, and ambient-frame hypotheses
are derived from the immersion and the constructed cap. -/
theorem harmonic_integer_odd_of_pinkall (hPinkall : PinkallEmbeddedTorusRegularHomotopy)
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) X hp q.1)) : Odd m := by
  let L := rhombicPeriodPair t ht
  obtain ⟨G,cs,V,hm,hclosed,hs,hi,hV,_,hCV,hfixV,hcompat⟩ :=
    harmonic_integer_embedded_cap_with_compatible_atlas ht ha hc m hX hp hh hg hXi (puncturedGeneratorCore_isCompact L)
  have hzero := pinkall_even_on_punctured_marking hPinkall L G cs hm hclosed hs hi (fun p hp => (hcompat p hp).2.2)
  have he := cap_ambient_arf_eq_line_parity ht ha hc m hC0 hC hX hp hh hg hV hfixV hCV
    (v := (1,0)) (w := (0,1)) (by decide)
  rw [← Int.not_even_iff_odd]
  intro hem
  simp only [holomorphicMultiplierSection_finrank ht m,hem,ite_true] at he
  exact zero_ne_one (hzero.symm.trans he)

/-- The embedded integer branch is odd. The hypotheses use the actual
punctured torus map, with no choice of square root or values at a
deleted point. The sole external premise is the unmarked geometric
regular-homotopy theorem, which does not mention spin or Arf. -/
theorem actual_embedded_integer_branch_odd_of_pinkall (hPinkall : PinkallEmbeddedTorusRegularHomotopy)
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    Odd m := by
  obtain ⟨F,cs,U,hm,he,hs,hi,_,_,_,_,hA,hq⟩ := actual_embedded_integer_branch_cap_arf ht ha hc m hX hXi hh hg
  have hz := pinkall_even_on_punctured_marking hPinkall _ F cs hm he hs hi hA
  rw [← Int.not_even_iff_odd]
  intro hem
  have ho := hq (1,0) (0,1) (by decide)
  simp only [hem,ite_true] at ho
  exact zero_ne_one (hz.symm.trans ho)


end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidal_torus_marked_arf_zero_of_pinkall
#print axioms TwoAxisHelicoid.harmonic_integer_odd_of_pinkall
#print axioms TwoAxisHelicoid.actual_embedded_integer_branch_odd_of_pinkall
