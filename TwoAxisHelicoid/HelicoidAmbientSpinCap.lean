import TwoAxisHelicoid.CompactCapTangentNormal
import TwoAxisHelicoid.HelicoidSpinCoreRestriction
import TwoAxisHelicoid.SpatialSpinEquivariance

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped ContDiff Manifold Matrix
set_option maxHeartbeats 1200000

/-- The full ambient spin cover of a smooth compact helicoid cap extends
the spatial spin structure of its original punctured surface. The maps
in the commuting square are actual homeomorphisms on both total spaces;
the spinor is fixed over the preserved compact core and its circle action
is respected everywhere. -/
theorem helicoidal_surface_genuine_compact_spin_extension (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ} (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates)
    (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hX : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (hsm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (hi : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    let f := puncturedMarkedTangentFrame L X hsm hi
    ∃ (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L))
      (hF : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F p)
      (hiF : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F p))
      (K : Set (PuncturedPeriodTorus L)) (_ : CoverCoreRetraction K) (U : Set (PeriodTorus L))
      (n : C(PeriodTorus L,Fin 3 → ℝ))
      (σ : SpatialPlaneSpin f ≃ₜ {s : NormalFieldSpin n // s.1.1 ≠ 0})
      (β : OrientedPlaneFrames f ≃ₜ {s : NormalFieldFrames n // s.1.1 ≠ 0}),
      let _ := cs
      IsCompact K ∧ IsOpen U ∧ Subtype.val '' K ⊆ U ∧ EqOn F X U ∧
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) ∧ IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F ∧
      (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F p)) ∧
      (∀ q, n q ⬝ᵥ n q = 1) ∧
      (∀ q : PuncturedPeriodTorus L, n q.1 = tangentPairNormal (puncturedMarkedTangentFrame L F hF hiF q)) ∧
      (∃ (e : OpenPartialHomeomorph (PeriodTorus L) ℂ) (he : RegularImmersionChart F e) (h0 : 0 ∈ e.source),
        let N := tangentPairNormal (spatialDifferentialFrame (he (e 0) (e.map_source h0)).2 (v := 1) one_ne_zero)
        n 0 = N ∨ n 0 = -N) ∧
      IsCoveringMap (normalFieldSpinProjection n) ∧
      (∀ x, normalFieldSpinProjection n (σ x).1 = (β (spatialPlaneSpinProjection f x)).1) ∧
      (∀ x : SpatialPlaneSpin f, (σ x).1.1.1 = x.1.1.1) ∧
      (∀ x : SpatialPlaneSpin f, x.1.1 ∈ K → (σ x).1.1.2 = x.1.2) ∧
      ∀ u x, (σ (spatialSpinRotation f u x)).1 = normalSpinRotation n u (σ x).1 := by
  let f := puncturedMarkedTangentFrame L X hsm hi
  obtain ⟨K,R,F,cs,U,hF,hiF,hK,hU,hKU,hfx,hm,he,hcap,hcapi,H,⟨hHp,hHK⟩,_⟩ :=
    helicoidal_embedded_cap_preserves_full_punctured_spin L A hA hAi hEnd hX hXi hsm hi
  let _ := cs
  let _ := hm
  let g := puncturedMarkedTangentFrame L F hF hiF
  obtain ⟨n,hn,hng,h0⟩ := compact_cap_unit_normal_extends L F cs hcap hcapi hF hiF
  let i := normalSpinPunctureIdent 0 n g hng
  let j := normalFramesPunctureIdent 0 n g hng
  let σ := H.trans i
  let β := ((orientedPlaneFrameHomeomorph f f.continuous).symm.trans
    (orientedPlaneFrameHomeomorph g g.continuous)).trans j
  refine ⟨F,cs,hF,hiF,K,R,U,n,σ,β,hK,hU,hKU,hfx,hm,he,hcap,hcapi,hn,hng,h0,
    normalFieldSpinProjection_isCoveringMap n,?_,?_,?_,?_⟩
  · intro x
    exact (normalSpinPunctureIdent_projection 0 n g hng (H x)).trans
      (congrArg (fun z => (j z).1) (spatial_spin_transport_square H hHp x))
  · intro x
    exact congrArg (fun v : PuncturedPeriodTorus L × Circle => v.1.1) (hHp x)
  · intro x hx
    exact congrArg Prod.snd (hHK x hx)
  · intro u x
    change (i (H (spatialSpinRotation f u x))).1 = _
    rw [spatial_spin_angle_equivariant f g H hHp]
    rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidal_surface_genuine_compact_spin_extension
