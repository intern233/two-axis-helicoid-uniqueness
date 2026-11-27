import TwoAxisHelicoid.PuncturedSurfaceCompactCore
import TwoAxisHelicoid.CompactCoreSpatialSpin
import TwoAxisHelicoid.PuncturedMarkedTangentFrame
import TwoAxisHelicoid.HelicoidalTorusSpinParity

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped ContDiff Manifold

/-- The actual orthonormal frame fields of two regular torus maps coincide
where their spatial parametrizations agree on an open neighborhood. -/
theorem punctured_marked_frames_eq_on_core (L : PeriodPair)
    {F G : PeriodTorus L → Fin 3 → ℝ}
    (hF : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (hiF : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (hG : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ G q)
    (hiG : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) G q))
    {K : Set (PuncturedPeriodTorus L)} {U : Set (PeriodTorus L)} (hU : IsOpen U)
    (hKU : Subtype.val '' K ⊆ U) (he : EqOn F G U) :
    EqOn (puncturedMarkedTangentFrame L F hF hiF) (puncturedMarkedTangentFrame L G hG hiG) K := by
  intro q hq
  obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L q
  rw [puncturedMarkedTangentFrame_projection,puncturedMarkedTangentFrame_projection]
  have hz : periodTorusProjection L z.1 ∈ U := hKU ⟨_,hq,rfl⟩
  have hπ : Continuous (periodTorusProjection L) := QuotientAddGroup.continuous_mk
  have heq : F ∘ periodTorusProjection L =ᶠ[𝓝 z.1] G ∘ periodTorusProjection L := by
    filter_upwards [hπ.continuousAt.eventually (hU.mem_nhds hz)] with w hw
    exact he hw
  apply Subtype.ext
  change spatialGramFrame _ _ = spatialGramFrame _ _
  rw [heq.fderiv_eq]

/-- Capping a general proper smooth helicoidal embedding gives a closed
smooth embedded torus whose restricted ambient spin cover agrees on
all oriented frames of the whole punctured torus. The identification is
determined by fixing the unchanged spatial quaternions over an actual
compact deformation retract. -/
theorem helicoidal_embedded_cap_preserves_full_punctured_spin (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ} (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates)
    (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hX : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (hsm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (hi : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    ∃ (K : Set (PuncturedPeriodTorus L)) (_ : CoverCoreRetraction K)
      (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L))
      (U : Set (PeriodTorus L))
      (hF : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F p)
      (hiF : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F p)),
      let _ := cs
      let f := puncturedMarkedTangentFrame L X hsm hi
      let g := puncturedMarkedTangentFrame L F hF hiF
      IsCompact K ∧ IsOpen U ∧ Subtype.val '' K ⊆ U ∧ EqOn F X U ∧
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) ∧ IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F ∧
      (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p)) ∧
      ∃! H : SpatialPlaneSpin f ≃ₜ SpatialPlaneSpin g,
        (∀ x, spatialSpinMarkedProjection g (H x) = spatialSpinMarkedProjection f x) ∧
        ∀ x : SpatialPlaneSpin f, x.1.1 ∈ K → (H x).1 = x.1 := by
  let M := PeriodTorus L
  obtain ⟨K,Q,hK,h0,h1,hfix⟩ :=
    punctured_surface_has_compact_core_retraction (chartAt ℂ (0 : M)) (mem_chart_source ℂ (0 : M))
  let R : CoverCoreRetraction K := ⟨Q,h0,h1,hfix⟩
  obtain ⟨F,cs,U,hm,he,hcap,hcapi,hU,_,hKU,hfx,hreg⟩ :=
    smooth_marked_helicoid_cap L A hA hAi hEnd hX hXi hsm hi hK
  let hF := fun p hp => (hreg p hp).1
  let hiF := fun p hp => (hreg p hp).2.1
  let f := puncturedMarkedTangentFrame L X hsm hi
  let g := puncturedMarkedTangentFrame L F hF hiF
  have hfg : EqOn f g K := punctured_marked_frames_eq_on_core L hsm hi hF hiF hU hKU hfx.symm
  obtain ⟨H,⟨hHp,hHK⟩,hu⟩ := spatial_spin_identified_by_core R f g hfg
  refine ⟨K,R,F,cs,U,hF,hiF,hK,hU,hKU,hfx,hm,he,hcap,hcapi,H,⟨hHp,?_⟩,?_⟩
  · intro x hx
    exact congrArg Subtype.val (hHK ⟨x,hx⟩)
  · intro T hT
    exact hu T ⟨hT.1,fun e => Subtype.ext (hT.2 e.1 e.2)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidal_embedded_cap_preserves_full_punctured_spin
