import TwoAxisHelicoid.EmbeddedMarkedTorusEvenSpin
import TwoAxisHelicoid.HelicoidEvenSpinCompactification

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold
universe u

/-- The spin quadratic form on the marked generators of an embedded
helicoidal torus is even. The plane-section argument applies to the
actual closed cap which agrees with the physical immersion on those
generators. -/
theorem helicoidal_torus_arf_zero_from_plane_sections (L : PeriodPair) {X : PeriodTorus L → Fin 3 → ℝ}
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hp : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (inj : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (sm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (di : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    ∀ v w, torusIntersectionModTwo v w=1 → capAmbientSpinQuadratic L X v*capAmbientSpinQuadratic L X w=0 := by
  obtain ⟨F,cs,U,hm,he,hcap,hfi,hU,_,hCU,hfx,hcompat⟩ :=
    smooth_marked_helicoid_cap L A hA hAi hEnd hp inj sm di (puncturedGeneratorCore_isCompact L)
  have zero := embedded_torus_even_on_punctured_marking L F cs hm he hcap hfi (fun p h => (hcompat p h).2.2)
  have same : capAmbientSpinQuadratic L F=capAmbientSpinQuadratic L X := by
    classical
    unfold capAmbientSpinQuadratic
    simp only [cap_ambient_spin_closes_of_eq_near_generators L hU hCU hfx]
  intro v w pair
  rw [cap_ambient_arf_basis L X v w pair,← same]
  exact zero

/-- Proposition 4.4 for a proper embedded torus having a smooth normal
graph with height tending to zero. The unique spin extension and its even
Arf invariant on every symplectic basis are obtained on a physical cap. -/
theorem height_decay_helicoidal_torus_unique_even_spin_from_sections
    (L : PeriodPair) {X : PeriodTorus L → Fin 3 → ℝ}
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidHeightEnd (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hp : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (inj : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (sm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (di : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    HasUniqueGenuineCompactSpinExtension.{u} L X sm di (fun F => ∀ v w, torusIntersectionModTwo v w=1 →
      capAmbientSpinQuadratic L F v*capAmbientSpinQuadratic L F w=0) ∧
      ∀ v w, torusIntersectionModTwo v w=1 → capAmbientSpinQuadratic L X v*capAmbientSpinQuadratic L X w=0 := by
  obtain ⟨B,b,bi,graph⟩ := helicoidal_height_end_admits_C1_chart
    (X:=fun q : PuncturedPeriodTorus L => X q.1) A hA hAi hEnd hp
  refine ⟨?_,helicoidal_torus_arf_zero_from_plane_sections L B b bi graph hp inj sm di⟩
  obtain ⟨F,cs,hF,hiF,K,R,U,n,σ,β,hK,hU,hKU,hfx,hm,he,hcap,hcapi,hn,hng,hpt,hcov,hproj,hbase,hKσ,hrot,hu,_⟩ :=
    helicoidal_surface_unique_genuine_spin_extension.{u} L B b bi graph hp inj sm di
  have zero := embedded_cap_even_of_punctured_regularity L F hF hiF cs hm he hcap hcapi
  refine ⟨F,cs,hF,hiF,K,R,U,n,σ,β,hK,hU,hKU,hfx,hm,he,hcap,hcapi,hn,hng,hpt,hcov,hproj,hbase,hKσ,hrot,hu,?_⟩
  intro v w pair
  rw [cap_ambient_arf_basis L F v w pair]
  exact zero

/-- On the actual embedded integer branch, plane-section parity of its
spatial cap forces the branch integer to be odd. -/
theorem actual_embedded_integer_odd_from_plane_sections
    {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hh : ∀ z∉(rhombicPeriodPair t ht).lattice, puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
      I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z∉gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (puncturedImmersionCoefficient
      (rhombicPeriodPair t ht) X z)=thetaGauss t a m z) : Odd m := by
  obtain ⟨F,cs,U,hm,he,hs,hi,_,_,_,_,hA,hq⟩ := actual_embedded_integer_branch_cap_arf ht ha hc m hX hXi hh hg
  have zero := embedded_torus_even_on_punctured_marking _ F cs hm he hs hi hA
  rw [← Int.not_even_iff_odd]
  intro even
  have value := hq (1,0) (0,1) (by decide)
  simp only [even,ite_true] at value
  exact zero_ne_one (zero.symm.trans value)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_decay_helicoidal_torus_unique_even_spin_from_sections
#print axioms TwoAxisHelicoid.actual_embedded_integer_odd_from_plane_sections
