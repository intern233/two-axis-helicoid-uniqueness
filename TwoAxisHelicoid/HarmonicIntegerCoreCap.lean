import TwoAxisHelicoid.HelicoidCapCoreCompatibility
import TwoAxisHelicoid.HarmonicIntegerSmoothCap

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

theorem homeomorph_fderiv_injective_of_smooth_inverse
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (D : E ≃ₜ A) (hD : ContDiff ℝ ∞ D) (hDi : ContDiff ℝ ∞ D.symm) (x : E) :
    Function.Injective (fderiv ℝ D x) := by
  have hd := hD.differentiable (by simp)
  have hdi := hDi.differentiable (by simp)
  have hc : (fderiv ℝ D.symm (D x)).comp (fderiv ℝ D x) =
      ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp x (hdi (D x)) (hd x)]
    have he : D.symm ∘ D = id := by funext z; exact D.symm_apply_apply z
    rw [he, fderiv_id]
  intro v w hvw
  have h := congrArg (fderiv ℝ D.symm (D x)) hvw
  simpa only [← ContinuousLinearMap.comp_apply, hc, ContinuousLinearMap.id_apply] using h

/-- The embedded harmonic integer branch has a smooth closed cap in its
original spatial coordinates. It agrees with the original immersion on
an open neighborhood of any prescribed compact core, where the original
complex atlas and the cap atlas are mutually smooth. -/
theorem harmonic_integer_embedded_core_cap
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
      ∀ q ∈ U, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus (rhombicPeriodPair t ht))) q ∧
        ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus (rhombicPeriodPair t ht))) q := by
  let L := rhombicPeriodPair t ht
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
  obtain ⟨D,R,cs,U,_,hm,hclosed,hcap,hcapi,hU,hpU,hCU,hfix,hcompat⟩ :=
    hEnd.exists_smooth_cap_compatible_near_core (X₀ := Y) hproper hYi
      (fun _ hq => heightCenteredTorusPrimitive_contMDiffAt hX hp hα b hq)
      (fun _ hq => heightCenteredTorusPrimitive_mfderiv_injective hX hp hα b hq) hC
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
  have hFi : ∀ q, Function.Injective
      (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) (A.symm ∘ F₀) q) := by
    intro q
    rw [mfderiv_comp q (hAi.contMDiff.mdifferentiable (by simp) _)
      (hcap.mdifferentiable (by simp) q),mfderiv_eq_fderiv]
    exact (homeomorph_fderiv_injective_of_smooth_inverse A.symm hAi hA _).comp (hcapi q)
  refine ⟨A.symm ∘ F₀,cs,U,hm,A.symm.isClosedEmbedding.comp hclosed,
    hAi.contMDiff.comp hcap,hFi,hU,hpU,hCU,?_,hcompat⟩
  intro q hq
  change A.symm (F₀ q) = _
  have hfq : F₀ q = Y q := hfix q hq
  rw [hfq,hYeq]
  exact A.symm_apply_apply _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_embedded_core_cap
