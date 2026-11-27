import TwoAxisHelicoid.PeriodicLimitFromLocalScalarGraphs
import TwoAxisHelicoid.HoffmanWhiteCompactClass

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- The periodic member allowed by compactness at a fixed cutoff. The
finite height and the open handle patch refer to its actual slab. The
tubular height graphs concern the same approximating spatial surfaces. -/
structure PeriodicHandleLimitAlong (η : ℝ) (s : ℕ → OriginalHelicoidRepresentative) where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [separated : T2Space carrier]
  position : carrier → Fin 3 → ℝ
  embedded : IsEmbedding position
  halfPeriod : ℝ
  cutoff : η≤halfPeriod
  periodic : unitHelicoidScrew halfPeriod '' range position=range position
  torus : PeriodPair
  patch : PuncturedPeriodTorus torus → {q : carrier // position q 2∈Ioo (-halfPeriod) halfPeriod}
  patchOpen : IsOpenEmbedding patch
  localGraphs : HasLocalTorusGraphApproximation position (fun n => (s n).modelTorus)
    (fun n => (s n).position ∘ (s n).topologicalType.symm)

attribute [instance] PeriodicHandleLimitAlong.topology PeriodicHandleLimitAlong.separated

/-- Compactness of normalized candidates at just one specified
Hoffman–White cutoff, including both allowed geometric alternatives.
The hypotheses on the sequence can be checked on the actual surfaces
before the compactness theorem is used. -/
def FixedCutoffCompactnessWith (periodic : (ℕ → OriginalHelicoidRepresentative) → Prop) : Prop :=
  ∀ t : ℕ → OriginalHelicoidRepresentative,
    (∀ n, HasPhysicalConformalTorus (t n).toOriginalSmoothHelicoid ∧ (t n).axes.pitch=1 ∧
      (t n).axes.horizontalPoint=0 ∧ (t n).axes.horizontalDirection=1 ∧
      halfTurnX '' range (t n).position=range (t n).position ∧
      halfTurnZ '' range (t n).position=range (t n).position) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ s : OriginalSmoothHelicoid,
        LocalSpatialImageLimit (fun n => (t (φ n)).unorientedNormals) s.unorientedNormals) ∨
       periodic (t ∘ φ))

abbrev FixedCutoffHandleCompactness (η : ℝ) : Prop :=
  FixedCutoffCompactnessWith (fun t => Nonempty (PeriodicHandleLimitAlong η t))

/-- In the periodic alternative the lowest sheet embeds two disjoint
handle cores in one of the approximating tori. This excludes that
alternative using only the one cutoff at which the limit was taken. -/
theorem fixed_cutoff_normalized_handle_subsequence (η : ℝ) (eta : Real.pi/2<η)
    (compact : FixedCutoffHandleCompactness η) (x : ℕ → positiveUnitPitchFamily) :
    ∃ (φ : ℕ → ℕ) (s : OriginalSmoothHelicoid) (t : ℕ → OriginalHelicoidRepresentative),
      StrictMono φ ∧ (∀ n, (t n).image=(x (φ n)).1.image) ∧
        LocalSpatialImageLimit (fun n => (t n).unorientedNormals) s.unorientedNormals := by
  choose t ht using fun n => positive_pitch_actual_geometric_representative (x n).1 (x n).2
  have normalized (n : ℕ) := ht n
  obtain ⟨φ,strict,limit⟩ := compact t (fun n => by
    obtain ⟨hit,pitch,here,dir,_⟩ := normalized n
    obtain ⟨ax,az⟩ := pitch_geometric_half_turns _ (x n).2.1 _ hit
    exact ⟨embedded_pitch_actual_conformal_type _ (x n).2.1 _ hit,pitch,here,dir,ax,az⟩)
  rcases limit with ⟨s,conv⟩ | periodic
  · exact ⟨φ,s,t ∘ φ,strict,fun n => (ht (φ n)).1,conv⟩
  · let u := t ∘ φ
    let P : PeriodicHandleLimitAlong η u := Classical.choice periodic
    have pos : 0<P.halfPeriod := ((half_pos Real.pi_pos).trans eta).trans_le P.cutoff
    have moving (n : ℕ) : IsEmbedding ((u n).position ∘ (u n).topologicalType.symm) :=
      (u n).closedEmbedding.isEmbedding.comp (u n).topologicalType.symm.isEmbedding
    exact (screw_periodic_punctured_patch_excluded_by_local_height_graphs P.position P.embedded
      (fun n => (u n).modelTorus) (fun n => (u n).position ∘ (u n).topologicalType.symm) moving P.localGraphs
      P.torus P.patch P.patchOpen (unitHelicoidScrew P.halfPeriod)
      (d:=2*P.halfPeriod) (mul_ne_zero two_ne_zero pos.ne') (unitHelicoidScrew_height P.halfPeriod) P.periodic).elim

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fixed_cutoff_normalized_handle_subsequence
