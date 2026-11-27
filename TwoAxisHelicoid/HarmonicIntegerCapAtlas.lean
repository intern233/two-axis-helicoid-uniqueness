import TwoAxisHelicoid.HarmonicIntegerCoreCap
import TwoAxisHelicoid.HelicoidCapAtlasCompatibility

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

theorem smooth_ambient_equiv_manifold_regular
    {M E A B : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [ChartedSpace E M]
    {F : M → A} {x : M}
    (hF : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ F x)
    (hi : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) F x))
    (D : A ≃ₜ B) (hD : ContDiff ℝ ∞ D) (hDi : ContDiff ℝ ∞ D.symm) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,B) ∞ (D ∘ F) x ∧
      Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,B) (D ∘ F) x) := by
  refine ⟨hD.contMDiff.contMDiffAt.comp x hF,?_⟩
  rw [mfderiv_comp x (hD.contMDiff.mdifferentiable (by simp) _)
    (hF.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
  exact (homeomorph_fderiv_injective_of_smooth_inverse D hD hDi _).comp hi

/-- An actual embedded integer branch has a compact smooth cap in the
original ambient coordinates, fixing a neighborhood of any compact
core and agreeing with the original smooth structure everywhere on the
punctured torus. -/
theorem harmonic_integer_embedded_cap_with_compatible_atlas
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) X hp q.1))
    {C : Set (PuncturedPeriodTorus (rhombicPeriodPair t ht))} (hC : IsCompact C) :
    ∃ (F : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
      (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus (rhombicPeriodPair t ht)))
      (U : Set (PeriodTorus (rhombicPeriodPair t ht))), let _ := cs
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus (rhombicPeriodPair t ht)) ∧
      IsClosedEmbedding F ∧ ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F q)) ∧
      IsOpen U ∧ 0 ∉ U ∧ Subtype.val '' C ⊆ U ∧
      (∀ q ∈ U, F q = periodTorusLift (rhombicPeriodPair t ht) X hp q) ∧
      ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q ∧
        Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q) ∧
        ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus (rhombicPeriodPair t ht))) q ∧
        ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus (rhombicPeriodPair t ht))) q := by
  let L := rhombicPeriodPair t ht
  obtain ⟨K,U,hK,hU,hpU,hCU,hUK⟩ := punctured_compact_core_neighborhood hC
  have hα : 2*(a-m)/c ≠ 0 := integer_helicoidal_pitch_ne_zero ha hc m
  obtain ⟨b,hEnd⟩ := harmonic_integer_torus_C1_helicoid_end ht ha hc m hX hp hh hg
  let A := (axisSpatialNormalization hα ![0,0,b]).trans coordinateTubeHomeomorph
  let Y := coordinateToTube ∘ heightCenteredTorusPrimitive L (2*(a-m)/c) b X hp
  have hYeq : Y = A ∘ periodTorusLift L X hp := by
    rw [show Y = coordinateToTube ∘ heightCenteredTorusPrimitive L (2*(a-m)/c) b X hp from rfl,
      heightCenteredTorusPrimitive_eq_space_map L hα]
    rfl
  have hproper : IsProperMap (fun q : PuncturedPeriodTorus L => Y q.1) :=
    coordinateToTube_isProperMap
      (harmonic_integer_torus_proper_and_end_injective ht ha hc m hα b hX hp hh hg).1
  have hYi : Function.Injective (fun q : PuncturedPeriodTorus L => Y q.1) := by
    rw [hYeq]
    exact A.injective.comp hXi
  obtain ⟨D,R,cs,_,hm,hclosed,hcap,hcapi,hfix,hcompat⟩ :=
    hEnd.exists_cap_atlas_compatible_on_puncture (X₀ := Y) hproper hYi
      (fun _ hq => heightCenteredTorusPrimitive_contMDiffAt hX hp hα b hq)
      (fun _ hq => heightCenteredTorusPrimitive_mfderiv_injective hX hp hα b hq) hK
  let _ := cs
  let _ := hm
  let F₀ := helicoidCompactCap (0 : PeriodTorus L) D R
    (fun q : PuncturedPeriodTorus L => Y q.1)
  have hA : ContDiff ℝ ∞ A :=
    coordinateToTube.contDiff.comp (axisSpatialNormalization_contDiff hα ![0,0,b])
  have htube : ContDiff ℝ ∞ tubeCartesian := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp [tubeCartesian] <;> fun_prop
  have hAi : ContDiff ℝ ∞ A.symm :=
    (axisSpatialNormalization_symm_contDiff hα ![0,0,b]).comp htube
  have hreg (q : PeriodTorus L) :
      ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (A.symm ∘ F₀) q ∧
      Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) (A.symm ∘ F₀) q) :=
    smooth_ambient_equiv_manifold_regular (hcap q) (hcapi q) A.symm hAi hA
  refine ⟨A.symm ∘ F₀,cs,U,hm,A.symm.isClosedEmbedding.comp hclosed,
    (fun q => (hreg q).1),(fun q => (hreg q).2),hU,hpU,hCU,?_,?_⟩
  · intro q hq
    obtain ⟨r,hr,hrq⟩ := hUK hq
    have hfq : F₀ q = Y q := by rw [← hrq]; exact hfix r hr
    change A.symm (F₀ q) = _
    rw [hfq,hYeq]
    exact A.symm_apply_apply _
  · intro q hq
    obtain ⟨ho,hoi,hid,hid'⟩ := hcompat q hq
    obtain ⟨hAo,hAoi⟩ := smooth_ambient_equiv_manifold_regular ho hoi A.symm hAi hA
    exact ⟨hAo,hAoi,hid,hid'⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_embedded_cap_with_compatible_atlas
