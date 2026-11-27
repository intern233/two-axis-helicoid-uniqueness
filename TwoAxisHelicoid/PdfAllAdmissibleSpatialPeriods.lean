import TwoAxisHelicoid.PdfOriginalSpatialPeriodReduction

namespace TwoAxisHelicoid.PdfVertical
open Set

/-- Requiring both generators to close already forces the analytic height
cutoff. Hence uniqueness on the vertical branch gives uniqueness among
all positive heights and all abscissas in (0,1). -/
theorem unique_positive_generators_of_branch_root
    (root : ∃! t : ℝ, t∈Ioo (0:ℝ) ellipticVerticalUpper ∧ originalPeriodAlong t=0)
    (c : ℝ) (hc : c≠0) :
    ∃! p : ℝ × ℝ, ∃ ht : 0<p.1, p.2∈Ioo (0:ℝ) 1 ∧ ∀ j : Fin 3,
      (originalCoordinatePeriod p.1 p.2 c ht j).re=0 ∧
      (conjugateCoordinatePeriod p.1 p.2 c ht j).re=0 := by
  obtain ⟨p,⟨_,witness⟩,only⟩ := unique_generators_on_of_scalar (fun _ h => h) root c hc
  refine ⟨p,witness,?_⟩
  rintro q ⟨tpos,ab,closed⟩
  have principal := (spatial_generators_iff_original_scalar tpos ab hc).mp closed
  exact only q ⟨⟨tpos,principal.1⟩,tpos,ab,closed⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.unique_positive_generators_of_branch_root
