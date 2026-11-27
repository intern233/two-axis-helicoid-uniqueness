import TwoAxisHelicoid.HolomorphicPlaneDeckTranslations
import TwoAxisHelicoid.RhombicLattice
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free

namespace TwoAxisHelicoid
open Complex Filter Set Topology Submodule
open scoped Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

def planeCoverPeriods (p : ℂ → M) : AddSubgroup ℂ where
  carrier := {a | ∀ z, p (z+a) = p z}
  zero_mem' := by simp
  add_mem' {a b} ha hb z := by rw [← add_assoc,hb,ha]
  neg_mem' {a} ha z := by simpa using (ha (z + -a)).symm

theorem planeCoverPeriods_eq_fiber {p : ℂ → M} (hp : HolomorphicPlaneCover p) :
    (planeCoverPeriods p : Set ℂ) = p ⁻¹' {p 0} := by
  ext x
  change (∀ z, p (z+x) = p z) ↔ p x = p 0
  refine ⟨fun h => by simpa using h 0,fun h z => ?_⟩
  simpa using hp.fiber_translations h.symm z

theorem planeCoverPeriods_fiber_eq {p : ℂ → M} (hp : HolomorphicPlaneCover p) (x y : ℂ) :
    p x = p y ↔ y-x ∈ planeCoverPeriods p := by
  refine ⟨fun h z => hp.fiber_translations h z,fun h => ?_⟩
  have he := h x
  simpa only [add_sub_cancel] using he.symm

theorem planeCoverPeriods_discrete {p : ℂ → M} (hp : HolomorphicPlaneCover p) :
    DiscreteTopology (planeCoverPeriods p) := by
  change DiscreteTopology ((planeCoverPeriods p : Set ℂ) : Type)
  rw [planeCoverPeriods_eq_fiber hp]
  exact (hp.covering (p 0)).discreteTopology_fiber

/-- Compactness of the surface forces its plane covering periods to
span the plane over the reals: a missing real direction would give
a continuous surjection from the compact surface to the real line. -/
theorem planeCoverPeriods_span_top [CompactSpace M] {p : ℂ → M} (hp : HolomorphicPlaneCover p) :
    span ℝ (planeCoverPeriods p : Set ℂ) = ⊤ := by
  classical
  let S := span ℝ (planeCoverPeriods p : Set ℂ)
  by_contra h
  obtain ⟨f,hf,hker⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr h)
  let F := fun y : M => f ((hp.onto y).choose)
  have he (z : ℂ) : F (p z) = f z := by
    let w := (hp.onto (p z)).choose
    have hw : p w = p z := (hp.onto (p z)).choose_spec
    have hdiff := (planeCoverPeriods_fiber_eq hp z w).mp hw.symm
    have hzero : f (w-z) = 0 := hker (subset_span hdiff)
    exact sub_eq_zero.mp (by rwa [map_sub] at hzero)
  have hC : Continuous F := (hp.covering.isQuotientMap hp.onto).continuous_iff.mpr
    (show Continuous (F ∘ p) from (funext he : F ∘ p = f).symm ▸ f.continuous_of_finiteDimensional)
  have hf' : Function.Surjective f := LinearMap.surjective hf
  have honto : Function.Surjective F := by
    intro t
    obtain ⟨z,rfl⟩ := hf' t
    exact ⟨p z,he z⟩
  exact noncompact_univ ℝ (honto.range_eq ▸ isCompact_range hC)

/-- The period group of any holomorphic plane covering of a compact Riemann
surface has a genuine real basis of two generators which also generates
the entire group over the integers. -/
theorem compact_plane_cover_periodPair [CompactSpace M] {p : ℂ → M} (hp : HolomorphicPlaneCover p) :
    ∃ L : PeriodPair, L.lattice.toAddSubgroup = planeCoverPeriods p := by
  let K := (planeCoverPeriods p).toIntSubmodule
  let : DiscreteTopology K := planeCoverPeriods_discrete hp
  let : IsZLattice ℝ K := ⟨planeCoverPeriods_span_top hp⟩
  let := ZLattice.module_free ℝ K
  let := ZLattice.module_finite ℝ K
  have hr : Module.finrank ℤ K = 2 := (ZLattice.rank ℝ K).trans Complex.finrank_real_complex
  let b := Module.finBasisOfFinrankEq ℤ K hr
  let B := b.ofZLatticeBasis ℝ
  have he : (![B 0,B 1] : Fin 2 → ℂ) = B := by ext j; fin_cases j <;> rfl
  let L : PeriodPair := ⟨B 0,B 1,he.symm ▸ B.linearIndependent⟩
  refine ⟨L,?_⟩
  have hs : ({B 0,B 1} : Set ℂ) = range B := by rw [← he]; simp [Set.pair_comm]
  have hL : L.lattice = K := by
    change span ℤ ({B 0,B 1} : Set ℂ) = K
    rw [hs]
    exact b.ofZLatticeBasis_span ℝ
  exact congrArg Submodule.toAddSubgroup hL

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_plane_cover_periodPair
