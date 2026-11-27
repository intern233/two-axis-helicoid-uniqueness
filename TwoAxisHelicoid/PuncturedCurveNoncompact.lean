import TwoAxisHelicoid.ChartFinitePoles

namespace TwoAxisHelicoid
open Set

theorem punctured_complex_curve_noncompact {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [T2Space M] (p : M) :
    NoncompactSpace {q : M // q ≠ p} := by
  constructor
  intro hc
  have hP : IsCompact ({p}ᶜ : Set M) := by
    have he : (Subtype.val : {q : M // q ≠ p} → M) '' univ = {p}ᶜ := by
      ext q
      simp
    simpa only [he] using hc.image
      (continuous_subtype_val : Continuous (Subtype.val : {q : M // q ≠ p} → M))
  have hd : Dense ({p}ᶜ : Set M) := finite_compl_dense_complex_charts (finite_singleton p)
  have heq : ({p}ᶜ : Set M) = univ := by
    rw [← hP.isClosed.closure_eq,hd.closure_eq]
  have hp : p ∈ ({p}ᶜ : Set M) := by rw [heq]; trivial
  exact hp rfl

theorem cofinite_punctured_curve_nonempty {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [T2Space M] (p : M)
    {S : Set {q : M // q ≠ p}} (hc : IsCompact Sᶜ) : S.Nonempty := by
  let := punctured_complex_curve_noncompact p
  by_contra hn
  have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  rw [hS,compl_empty] at hc
  exact noncompact_univ _ hc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_complex_curve_noncompact
