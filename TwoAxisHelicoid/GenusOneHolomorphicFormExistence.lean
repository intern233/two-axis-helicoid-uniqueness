import TwoAxisHelicoid.TorusNonzeroFormUniformization
import TwoAxisHelicoid.HolomorphicSectionQuotient

namespace TwoAxisHelicoid
open Complex Set Metric
open scoped Topology ContDiff Manifold
universe u

/-- The existence of a nonzero holomorphic differential on a curve
homeomorphic to a torus. The form is allowed to have zeros. -/
def GenusOneHasHolomorphicDifferential : Prop :=
  ∀ (L : PeriodPair) (M : Type u) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M], Nonempty (M ≃ₜ PeriodTorus L) →
      ∃ w : holomorphicCotangentSections M, w≠0

/-- The dimension part of Riemann--Roch is sufficient for existence. -/
theorem genus_one_holomorphic_differential_of_dimension
    (dim : ∀ (L : PeriodPair) (M : Type u) [TopologicalSpace M] [CompactSpace M] [T2Space M]
      [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M], Nonempty (M ≃ₜ PeriodTorus L) →
        Module.finrank ℂ (holomorphicCotangentSections M)=1) : GenusOneHasHolomorphicDifferential.{u} := by
  intro L M top compact sep atlas manifold marking
  have : Nontrivial (holomorphicCotangentSections M) := Module.nontrivial_of_finrank_pos (R := ℂ)
    (by rw [dim L M marking]; decide)
  exact exists_ne 0

/-- Every nonzero holomorphic differential on a compact curve homeomorphic
to the period torus is nonzero at each point. -/
theorem genus_one_holomorphic_section_nowhere_zero {M : Type u} [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L) (w : holomorphicCotangentSections M) (wn : w≠0) :
    ∀ y, w.1 y (chartAt ℂ y y)≠0 := by
  classical
  have disks (p : M) : ∃ r : ℝ, 0<r ∧ ball (chartAt ℂ p p) r⊆(chartAt ℂ p).target :=
    Metric.mem_nhds_iff.mp ((chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p)))
  choose r rp inc using disks
  let A : HolomorphicCoefficientDisks M := ⟨r,rp,inc,w.1,fun i z hz => w.2.1 i z (inc i hz)⟩
  have compat : A.compatibleOneForm := fun i j x hx => w.2.2.1 i j x ⟨hx.1.1,hx.2.1⟩
  have detect : ∃ x : M, A.coefficient x (chartAt ℂ x x)≠0 := by
    by_contra! allZero
    apply wn
    apply Subtype.ext
    funext i z
    change w.1 i z=0
    by_cases tz : z∈(chartAt ℂ i).target
    · let x := (chartAt ℂ i).symm z
      have hx : x∈(chartAt ℂ i).source := (chartAt ℂ i).map_target tz
      have eq := w.2.2.1 i x x ⟨hx,mem_chart_source ℂ x⟩
      have cz : chartAt ℂ i x=z := (chartAt ℂ i).right_inv tz
      have zero : w.1 x (chartAt ℂ x x)=0 := allZero x
      simpa only [cz,zero,zero_mul] using eq
    · exact w.2.2.2 i z tz
  obtain ⟨x,non⟩ := detect
  exact HolomorphicCoefficientDisks.compact_torus_nonzero_form_nowhere_zero mark A compat non

/-- The dimension and canonical-divisor conclusions follow from existence
of just one nonzero section. The analytic order of every nonzero
section vanishes at every point of the original surface. -/
theorem genus_one_canonical_divisor_of_one_section (existsForm : GenusOneHasHolomorphicDifferential.{u}) :
    GenusOneCanonicalDivisorFormula.{u} := by
  classical
  intro L M top compact sep atlas manifold marking
  obtain ⟨w,wn⟩ := existsForm L M marking
  obtain ⟨mark⟩ := marking
  let _ : ConnectedSpace (PeriodTorus L) := (Quotient.mk_surjective :
    Function.Surjective (periodTorusProjection L)).connectedSpace QuotientAddGroup.continuous_mk
  let _ : ConnectedSpace M := mark.symm.surjective.connectedSpace mark.symm.continuous
  constructor
  · exact (finrank_eq_one_iff_of_nonzero' w wn).mpr
      (nowhere_zero_section_spans w (genus_one_holomorphic_section_nowhere_zero mark w wn))
  · intro v nv
    refine ⟨0,fun x => ?_,by simp⟩
    have non := genus_one_holomorphic_section_nowhere_zero mark v nv x
    exact ((v.2.1 x _ ((chartAt ℂ x).map_source (mem_chart_source ℂ x))).analyticOrderAt_eq_zero.mpr non).symm

theorem genus_one_canonical_divisor_iff_one_section :
    GenusOneCanonicalDivisorFormula.{u} ↔ GenusOneHasHolomorphicDifferential.{u} :=
  ⟨fun rr => genus_one_holomorphic_differential_of_dimension fun L M _ _ _ _ _ mark => (rr L M mark).1,
    genus_one_canonical_divisor_of_one_section⟩

theorem genus_one_uniformization_of_holomorphic_differential (existsForm : GenusOneHasHolomorphicDifferential.{u})
    (L : PeriodPair) : CompactGenusOneUniformization.{u} L :=
  genus_one_period_uniformization_from_canonical_divisor (genus_one_canonical_divisor_of_one_section existsForm) L

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.genus_one_canonical_divisor_iff_one_section
#print axioms TwoAxisHelicoid.genus_one_uniformization_of_holomorphic_differential
