import TwoAxisHelicoid.RegularPunctureMarking
import TwoAxisHelicoid.HelicoidEvenSpinFromSections

namespace TwoAxisHelicoid
open Complex Set Function Topology
open scoped ContDiff Manifold
universe u v

/-- The actual one-point compactification of the physical parameter
surface and a single marked compact torus on which its full spin
cover is represented. The compact embedded cap agrees with the
original position on a compact deformation core in that surface. -/
def EvenSpinExtensionInMarking {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {L : PeriodPair} (X : M → Fin 3 → ℝ) (e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞) : Prop :=
  let fill := e.toHomeomorph.onePointCongr.trans (punctureCompactification (0:PeriodTorus L))
  (fill OnePoint.infty=0) ∧ (∀ x : M, fill (OnePoint.some x)=(e x).1) ∧
    ∃ Y : PeriodTorus L → Fin 3 → ℝ, (∀ x, Y (e x).1=X x) ∧
      ∃ (sm : ∀ p≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ Y p)
        (di : ∀ p≠0, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) Y p)),
        (∀ v w, torusIntersectionModTwo v w=1 → capAmbientSpinQuadratic L Y v*capAmbientSpinQuadratic L Y w=0) ∧
        HasUniqueGenuineCompactSpinExtension.{u} L Y sm di (fun F =>
          (∀ v w, torusIntersectionModTwo v w=1 → capAmbientSpinQuadratic L F v*capAmbientSpinQuadratic L F w=0) ∧
          IsClosedEmbedding (F ∘ fill) ∧ ∃ K : Set M, IsCompact K ∧ Nonempty (CoverCoreRetraction K) ∧
            ∀ x∈K, F (fill (OnePoint.some x))=X x)

/-- Proposition 4.4 for an arbitrarily parametrized smoothly
one-handled surface. The end requires only the decay of its height.
The cap and its parity apply to every smooth marking of the original
position. No minimal-surface or spin-parity theorem is supplied. -/
theorem abstract_helicoidal_surface_even_in_smooth_marking {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L : PeriodPair}
    (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ q, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (sA : ContDiff ℝ ∞ A) (sAi : ContDiff ℝ ∞ A.symm)
    (graph : HasHelicoidHeightEnd (A ∘ X))
    (e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞) :
    EvenSpinExtensionInMarking.{u} X e := by
  obtain ⟨Y,eqn,sy,iy⟩ := physical_position_in_smooth_puncture_marking e X sm di
  let Z := fun q : PuncturedPeriodTorus L => Y q.1
  have same : Z=X ∘ e.symm := funext eqn
  have closed : IsClosedEmbedding Z := same ▸ cl.comp e.symm.toHomeomorph.isClosedEmbedding
  have endY : HasHelicoidHeightEnd (A ∘ Z) := by
    rw [same]
    exact graph.comp_homeomorph e.symm.toHomeomorph
  obtain ⟨cap,parity⟩ := height_decay_helicoidal_torus_unique_even_spin_from_sections.{u} L A sA sAi
    endY closed.isProperMap closed.injective sy iy
  let fill := e.toHomeomorph.onePointCongr.trans (punctureCompactification (0:PeriodTorus L))
  have position (x : M) : Y (e x).1=X x := (eqn _).trans (congrArg X (e.symm_apply_apply x))
  refine ⟨rfl,fun _ => rfl,Y,position,sy,iy,parity,?_⟩
  obtain ⟨F,cs,sF,iF,K,R,U,n,σ,β,hK,hU,hKU,agree,hm,hcl,hsm,hdi,hunit,hn,hframe,hcover,hproj,hbase,hfields,hrot,univ,even⟩ := cap
  refine ⟨F,cs,sF,iF,K,R,U,n,σ,β,hK,hU,hKU,agree,hm,hcl,hsm,hdi,hunit,hn,hframe,hcover,hproj,hbase,hfields,hrot,univ,
    even,hcl.comp fill.isClosedEmbedding,e ⁻¹' K,e.toHomeomorph.isCompact_preimage.mpr hK,⟨R.pullback e.toHomeomorph⟩,?_⟩
  intro x hx
  exact (agree (hKU (mem_image_of_mem _ hx))).trans (position x)

/-- With genus understood purely topologically, the only additional
premise is classical smoothability of surface markings. The arbitrary
physical embedding, compactification, genuine covering and its even
Arf invariant are produced on the chosen smooth representative. -/
theorem topologically_one_handled_helicoidal_surface_even (smoothing : HomeomorphicSmoothSurfacesDiffeomorphic.{v,0})
    {M : Type v} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ q, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (sA : ContDiff ℝ ∞ A) (sAi : ContDiff ℝ ∞ A.symm)
    (graph : HasHelicoidHeightEnd (A ∘ X)) :
    ∃ e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞, EvenSpinExtensionInMarking.{u} X e := by
  let _ : T2Space M := cl.isEmbedding.t2Space
  let _ : SecondCountableTopology M := cl.isEmbedding.secondCountableTopology
  let _ : SecondCountableTopology (PuncturedPeriodTorus L) := top.symm.isEmbedding.secondCountableTopology
  obtain ⟨e⟩ := smoothing M (PuncturedPeriodTorus L) ⟨top⟩
  exact ⟨e,abstract_helicoidal_surface_even_in_smooth_marking X cl sm di A sA sAi graph e⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.abstract_helicoidal_surface_even_in_smooth_marking
#print axioms TwoAxisHelicoid.topologically_one_handled_helicoidal_surface_even
