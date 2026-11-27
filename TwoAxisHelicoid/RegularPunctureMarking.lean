import TwoAxisHelicoid.ActualTorusManifoldImmersion
import TwoAxisHelicoid.HelicoidHeightDecayStraightening
import TwoAxisHelicoid.CompactPunctureHomeomorphism
import TwoAxisHelicoid.CompactCoreCoverTransport
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace TwoAxisHelicoid
open Complex Set Function Topology
open scoped ContDiff Manifold
universe u v

theorem HasHelicoidHeightEnd.comp_homeomorph {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {X : N → HelicoidTubeCoordinates} (hg : HasHelicoidHeightEnd X) (e : M ≃ₜ N) :
    HasHelicoidHeightEnd (X ∘ e) := by
  obtain ⟨S,core,R,r,E,u,smooth,bound,graph,decay⟩ := hg
  let H : (e ⁻¹' S) ≃ₜ S := e.subtype (p:=fun q => q∈e ⁻¹' S) (q:=fun q => q∈S) (fun _ => Iff.rfl)
  refine ⟨e ⁻¹' S,e.isCompact_preimage.mpr core,R,r,H.trans E,u,smooth,bound,?_,decay⟩
  exact fun q => graph (H q)

noncomputable def CoverCoreRetraction.pullback {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {K : Set N} (r : CoverCoreRetraction K) (e : M ≃ₜ N) : CoverCoreRetraction (e ⁻¹' K) where
  flow := ⟨fun tx => e.symm (r.flow (tx.1,e tx.2)), e.symm.continuous.comp
    (r.flow.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩
  initial := fun x => (congrArg e.symm (r.initial _)).trans (e.symm_apply_apply x)
  terminal := fun x => by
    change e (e.symm (r.flow (1,e x)))∈K
    rw [e.apply_symm_apply]
    exact r.terminal _
  fixed := fun t x hx => (congrArg e.symm (r.fixed t _ hx)).trans (e.symm_apply_apply x)

/-- The part of the classical smoothing theorem for surfaces needed in
the general, possibly nonminimal version of Proposition 4.4.
Hatcher, Theorem B, Enseign. Math. 72 (2026), 161–174, yields this
existence assertion. It is an explicit hypothesis when used. -/
def HomeomorphicSmoothSurfacesDiffeomorphic : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    (N : Type v) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℝ,ℂ) ∞ N],
    Nonempty (M ≃ₜ N) → Nonempty (Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M N ∞)

/-- In an abstract smooth marking of an actual surface, the position
extends as a function across the label for the end. At every finite
point its actual smoothness and injective differential are inherited
from that same physical immersion. -/
theorem physical_position_in_smooth_puncture_marking {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L : PeriodPair}
    (e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞)
    (X : M → Fin 3 → ℝ) (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (inj : ∀ q, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q)) :
    ∃ Y : PeriodTorus L → Fin 3 → ℝ, (∀ q : PuncturedPeriodTorus L, Y q.1=X (e.symm q)) ∧
      (∀ p≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ Y p) ∧
      ∀ p≠0, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) Y p) := by
  classical
  let V := (Subtype.val : PuncturedPeriodTorus L → PeriodTorus L)
  let Y := Function.extend V (X ∘ e.symm) 0
  have eqn : Y ∘ V=X ∘ e.symm := Function.extend_comp Subtype.val_injective _ _
  have sr : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (Y ∘ V) := eqn ▸ (sm.comp e.symm.contMDiff)
  have reg (q : PuncturedPeriodTorus L) : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ Y q.1 :=
    (contMDiffAt_subtype_iff (U:=puncturedPeriodTorusOpen L)).mp (sr q)
  refine ⟨Y,fun q => congrFun eqn q,fun p h => reg ⟨p,h⟩,?_⟩
  intro p hp
  let q : PuncturedPeriodTorus L := ⟨p,hp⟩
  let D := mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) V q
  let P := mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) Y p
  have full : Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (Y ∘ V) q) := by
    rw [eqn,mfderiv_comp q (sm.mdifferentiable (by simp) _) (e.symm.contMDiff.mdifferentiable (by simp) _)]
    exact (inj _).comp (e.symm.mfderivToContinuousLinearEquiv (by simp) q).injective
  have dv : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) V q :=
    (contMDiff_subtype_val (I:=𝓘(ℝ,ℂ)) (U:=puncturedPeriodTorusOpen L) (n:=∞)).mdifferentiable (by simp) q
  have chain : mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (Y ∘ V) q=P.comp D :=
    mfderiv_comp (f:=V) (g:=Y) q ((reg q).mdifferentiableAt (by simp)) dv
  rw [chain] at full
  have together : Injective (P.comp D) := full
  have di : Injective D := fun _ _ eq => together (congrArg P eq)
  have ds : Surjective D := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=D.toLinearMap) rfl).mp di
  intro v w equ
  obtain ⟨v,rfl⟩ := ds v
  obtain ⟨w,rfl⟩ := ds w
  exact congrArg D (together equ)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_position_in_smooth_puncture_marking
