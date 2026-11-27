import TwoAxisHelicoid.EmbeddedCapSpinParity
import TwoAxisHelicoid.HarmonicIntegerCapAtlas

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 1800000

/-- The ambient spin on either marked loop only uses the spatial immersion
germ along that loop. This comparison does not require conformal charts. -/
theorem cap_ambient_spin_closes_of_eq_near_generators (L : PeriodPair)
    {F G : PeriodTorus L → Fin 3 → ℝ} {U : Set (PeriodTorus L)} (hU : IsOpen U)
    (hcore : Subtype.val '' puncturedGeneratorCore L ⊆ U) (he : EqOn F G U) (i : Fin 2) :
    CapGeneratorAmbientSpinCloses L F i ↔ CapGeneratorAmbientSpinCloses L G i := by
  have hD (r : unitInterval) :
      fderiv ℝ (F ∘ periodTorusProjection L) (periodBasisLine L i r) =
      fderiv ℝ (G ∘ periodTorusProjection L) (periodBasisLine L i r) := by
    apply Filter.EventuallyEq.fderiv_eq
    have hπ : Continuous (periodTorusProjection L) := QuotientAddGroup.continuous_mk
    filter_upwards [hπ.continuousAt.eventually (hU.mem_nhds (generator_projection_mem_fixed_core hcore i r))]
      with w hw
    exact he hw
  simp only [CapGeneratorAmbientSpinCloses,hD]

/-- A smooth embedded cap in the original ambient coordinates, compatible with
the unmodified marking on a neighborhood of any prescribed compact set. -/
theorem smooth_marked_helicoid_cap (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ}
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hX : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (hsm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (hi : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p))
    {K : Set (PuncturedPeriodTorus L)} (hK : IsCompact K) :
    ∃ (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L))
      (U : Set (PeriodTorus L)), let _ := cs
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) ∧ IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F q)) ∧
      IsOpen U ∧ 0 ∉ U ∧ Subtype.val '' K ⊆ U ∧ EqOn F X U ∧
      ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F p ∧
        Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F p) ∧
        ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus L)) p ∧
        ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus L)) p := by
  obtain ⟨J,U,hJ,hU,hpU,hKU,hUJ⟩ := punctured_compact_core_neighborhood hK
  let Y : PeriodTorus L → HelicoidTubeCoordinates := A ∘ X
  have hYp : IsProperMap (fun q : PuncturedPeriodTorus L => Y q.1) := A.isProperMap.comp hX
  have hYreg (p : PeriodTorus L) (hp : p ≠ 0) :=
    smooth_ambient_equiv_manifold_regular (hsm p hp) (hi p hp) A hA hAi
  obtain ⟨D,R,cs,_,hm,he,hcap,hcapi,hfix,hcompat⟩ :=
    hEnd.exists_cap_atlas_compatible_on_puncture (M := PeriodTorus L) (p := 0) (X₀ := Y) hYp
      (A.injective.comp hXi) (fun p hp => (hYreg p hp).1) (fun p hp => (hYreg p hp).2) hJ
  let _ := cs
  let _ := hm
  let G := helicoidCompactCap (0 : PeriodTorus L) D R (fun q : PuncturedPeriodTorus L => Y q.1)
  have hreg (p : PeriodTorus L) :=
    smooth_ambient_equiv_manifold_regular (hcap p) (hcapi p) A.symm hAi hA
  refine ⟨A.symm ∘ G, cs, U, hm, A.symm.isClosedEmbedding.comp he, (fun p => (hreg p).1),
    (fun p => (hreg p).2), hU, hpU, hKU, ?_, ?_⟩
  · intro p hp
    obtain ⟨q,hq,hqp⟩ := hUJ hp
    have heq : G p = Y p := by rw [← hqp]; exact hfix q hq
    change A.symm (G p) = X p
    rw [heq]
    exact A.symm_apply_apply _
  · intro p hp
    obtain ⟨ho,hoi,hid,hid'⟩ := hcompat p hp
    obtain ⟨hAo,hAoi⟩ := smooth_ambient_equiv_manifold_regular ho hoi A.symm hAi hA
    exact ⟨hAo,hAoi,hid,hid'⟩

theorem cap_ambient_arf_basis (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (v w : ZMod 2 × ZMod 2) (hvw : torusIntersectionModTwo v w = 1) :
    capAmbientSpinQuadratic L X v * capAmbientSpinQuadratic L X w =
      capAmbientSpinQuadratic L X (1,0) * capAmbientSpinQuadratic L X (0,1) := by
  classical
  unfold capAmbientSpinQuadratic
  rw [torusQuadratic_arf_basis _ _ v w hvw]
  simp [torusQuadratic]

/-- The original application of embedded-torus parity for a general proper
smooth helicoidal embedding on a marked punctured torus. The cap is built
inside the proof. Its frame computation agrees with the original immersion
on the chosen pair of generating curves. -/
theorem helicoidal_torus_marked_arf_zero_of_embedded_parity
    (hParity : EmbeddedTorusAmbientSpinParity) (L : PeriodPair)
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
  have hzero := hParity L F cs hm he hcap hfi (fun p hp => (hcompat p (fun heq => hpU (heq ▸ hCU hp))).2.2)
  have hq : capAmbientSpinQuadratic L F = capAmbientSpinQuadratic L X := by
    classical
    unfold capAmbientSpinQuadratic
    simp only [cap_ambient_spin_closes_of_eq_near_generators L hU hCU hfx]
  intro v w hvw
  rw [cap_ambient_arf_basis L X v w hvw, ← hq]
  exact hzero

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_marked_helicoid_cap
#print axioms TwoAxisHelicoid.helicoidal_torus_marked_arf_zero_of_embedded_parity
