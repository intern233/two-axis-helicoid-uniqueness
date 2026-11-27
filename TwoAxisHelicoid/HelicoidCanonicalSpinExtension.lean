import TwoAxisHelicoid.HelicoidAmbientSpinCap
import TwoAxisHelicoid.CompactSpinEquivariantUniqueness

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped ContDiff Manifold Matrix
universe u

/-- A specified rotation-equivariant isomorphism on a puncture complement
extends uniquely to a rotation-equivariant isomorphism of compact-base
spin coverings. The competing covering is completely arbitrary. -/
def GenuineSpinRestrictionUniversal {M : Type*} [TopologicalSpace M] (p : M) (n : M → Fin 3 → ℝ) : Prop :=
  ∀ (E : Type u) [TopologicalSpace E] (a : E → NormalFieldFrames n), IsCoveringMap a →
    ∀ (r : Circle → E → E), (∀ u, Continuous (r u)) →
    (∀ u x, a (r u x) = normalFrameRotation n (u^2) (a x)) →
    ∀ (i : {x : E // (a x).1.1 ≠ p} ≃ₜ {y : NormalFieldSpin n // y.1.1 ≠ p}),
    (∀ x, normalFieldSpinProjection n (i x).1 = a x.1) →
    (∀ u (x : {e : E // (a e).1.1 ≠ p}) (h : (a (r u x.1)).1.1 ≠ p),
      (i ⟨r u x.1,h⟩).1 = normalSpinRotation n u (i x).1) →
    ∃! H : E ≃ₜ NormalFieldSpin n, (∀ e, normalFieldSpinProjection n (H e) = a e) ∧
      (∀ x : {e : E // (a e).1.1 ≠ p}, H x.1 = (i x).1) ∧ ∀ u x, H (r u x) = normalSpinRotation n u (H x)

/-- A genuine full tangent spin structure on the compact cap together
with its punctured restriction and its universal extension property. -/
def HasUniqueGenuineCompactSpinExtension (L : PeriodPair)
    (X : PeriodTorus L → Fin 3 → ℝ)
    (hsm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (hi : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p))
    (P : (PeriodTorus L → Fin 3 → ℝ) → Prop := fun _ => True) : Prop :=
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
      (∀ u x, (σ (spatialSpinRotation f u x)).1 = normalSpinRotation n u (σ x).1) ∧
      GenuineSpinRestrictionUniversal.{u} (0 : PeriodTorus L) n ∧ P F

/-- Existence and uniqueness of the full ambient spin extension for a
general smooth embedded helicoidal end, including its genuine tangent
plane at the filled point. The entire compact core is preserved. -/
theorem helicoidal_surface_unique_genuine_spin_extension (L : PeriodPair)
    {X : PeriodTorus L → Fin 3 → ℝ} (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates)
    (hA : ContDiff ℝ ∞ A) (hAi : ContDiff ℝ ∞ A.symm)
    (hEnd : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => A (X q.1)))
    (hX : IsProperMap (fun q : PuncturedPeriodTorus L => X q.1))
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus L => X q.1))
    (hsm : ∀ p ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X p)
    (hi : ∀ p ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p)) :
    HasUniqueGenuineCompactSpinExtension.{u} L X hsm hi := by
  obtain ⟨F,cs,hF,hiF,K,R,U,n,σ,β,hK,hU,hKU,hfx,hm,he,hcap,hcapi,hn,hng,h0,hcov,hproj,hbase,hKσ,hrot⟩ :=
    helicoidal_surface_genuine_compact_spin_extension L A hA hAi hEnd hX hXi hsm hi
  refine ⟨F,cs,hF,hiF,K,R,U,n,σ,β,hK,hU,hKU,hfx,hm,he,hcap,hcapi,hn,hng,h0,hcov,hproj,hbase,hKσ,hrot,?_,trivial⟩
  intro E inst a ha r hr hrπ i hi hir
  exact actual_compact_spin_equivariant_unique 0 n hn a ha r hr hrπ i hi hir

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidal_surface_unique_genuine_spin_extension
