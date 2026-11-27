import TwoAxisHelicoid.NonvanishingTorusDifferential
import TwoAxisHelicoid.OriginalExteriorTorusReduction
import Mathlib.Analysis.Analytic.Order
import Mathlib.LinearAlgebra.Dimension.Finite

namespace TwoAxisHelicoid
open Complex Set Topology Metric
open scoped Topology ContDiff Manifold
universe u

/-- Global holomorphic one-forms in chart coordinates. Coefficients are
extended by zero outside each coordinate chart so this vector space has
no additional degrees of freedom there. -/
noncomputable def holomorphicCotangentSections (M : Type u) [TopologicalSpace M] [ChartedSpace ℂ M] : Submodule ℂ (M → ℂ → ℂ) where
  carrier := {w | (∀ i z, z∈(chartAt ℂ i).target → AnalyticAt ℂ (w i) z) ∧
    (∀ i j x, x∈(chartAt ℂ i).source∩(chartAt ℂ j).source →
      w i (chartAt ℂ i x)=w j (chartAt ℂ j x)*deriv ((chartAt ℂ j) ∘ (chartAt ℂ i).symm) (chartAt ℂ i x)) ∧
    ∀ i z, z∉(chartAt ℂ i).target → w i z=0}
  zero_mem' := ⟨fun _ _ _ => analyticAt_const,fun _ _ _ _ => by simp,fun _ _ _ => rfl⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨fun i z hz => (hf.1 i z hz).add (hg.1 i z hz),?_,?_⟩
    · intro i j x hx
      simp only [Pi.add_apply,hf.2.1 i j x hx,hg.2.1 i j x hx,add_mul]
    · intro i z hz
      simp only [Pi.add_apply,hf.2.2 i z hz,hg.2.2 i z hz,add_zero]
  smul_mem' := by
    intro c f hf
    refine ⟨?_,?_,?_⟩
    · intro i z hz
      change AnalyticAt ℂ (fun v => c*f i v) z
      exact analyticAt_const.mul (hf.1 i z hz)
    · intro i j x hx
      simp only [Pi.smul_apply,smul_eq_mul,hf.2.1 i j x hx,mul_assoc]
    · intro i z hz
      simp only [Pi.smul_apply,hf.2.2 i z hz,smul_zero]

/-- Two classical genus-one consequences of Riemann--Roch. The canonical
zero divisor records the actual analytic vanishing order at every point.
Neither a period lattice nor a developing map occurs in this input. -/
def GenusOneCanonicalDivisorFormula : Prop :=
  ∀ (L : PeriodPair) (M : Type u) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M], Nonempty (M ≃ₜ PeriodTorus L) →
      Module.finrank ℂ (holomorphicCotangentSections M)=1 ∧
      ∀ w : holomorphicCotangentSections M, w≠0 → ∃ D : M →₀ ℕ,
        (∀ p, (D p:ℕ∞)=analyticOrderAt (w.1 p) (chartAt ℂ p p)) ∧ (∑ p∈D.support, D p)=0

theorem genus_one_period_uniformization_from_canonical_divisor (rr : GenusOneCanonicalDivisorFormula.{u})
    (L : PeriodPair) : CompactGenusOneUniformization.{u} L := by
  classical
  intro M top compact sep atlas manifold torus
  obtain ⟨dim,degree⟩ := rr L M torus
  have : Nontrivial (holomorphicCotangentSections M) := Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [dim]; decide)
  obtain ⟨w,nz⟩ := exists_ne (0 : holomorphicCotangentSections M)
  obtain ⟨D,orders,total⟩ := degree w nz
  have vanishes (p : M) : D p=0 := by
    by_cases hp : p∈D.support
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => Nat.zero_le (D q))).mp total p hp
    · exact Finsupp.notMem_support_iff.mp hp
  have d (p : M) : ∃ r : ℝ, 0<r ∧ ball (chartAt ℂ p p) r⊆(chartAt ℂ p).target :=
    Metric.mem_nhds_iff.mp ((chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p)))
  choose r hr inc using d
  let A : HolomorphicCoefficientDisks M := ⟨r,hr,inc,w.1,fun i z hz => w.2.1 i z (inc i hz)⟩
  obtain ⟨mark⟩ := torus
  apply A.uniformization_of_nonvanishing_one_form mark
  · intro i j x hx
    exact w.2.2.1 i j x ⟨hx.1.1,hx.2.1⟩
  · intro p
    have ord := (orders p).symm
    rw [vanishes,ENat.natCast_zero] at ord
    exact (w.2.1 p _ ((chartAt ℂ p).map_source (mem_chart_source ℂ p))).analyticOrderAt_eq_zero.mp ord

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.genus_one_period_uniformization_from_canonical_divisor
