import TwoAxisHelicoid.CompactRootAttachmentSolution
import TwoAxisHelicoid.ActualConverseImmersion
import TwoAxisHelicoid.OriginalHeightPeriod

namespace TwoAxisHelicoid.PdfVertical
open Set

/-- A single parameter pair obtained by the root attachment closes both
actual spatial lattice generators at every nonzero scale. For every scale
the centered immersion has all eight geometric conclusions of §6.3. -/
theorem compact_root_attachment_reconstructs_immersion :
    ∃ p : ClosedPeriodParameters, p.t ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      p.a ∈ Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      ∀ (c : ℝ) (hc : c≠0),
        (∀ j : Fin 3, (originalCoordinatePeriod p.t p.a c p.height_pos j).re=0 ∧
          (conjugateCoordinatePeriod p.t p.a c p.height_pos j).re=0) ∧
        ClosedImmersionProperties p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed := by
  obtain ⟨t,ht,ha,_,hz⟩ := compact_root_attachment_contains_period_solution
  have dom := root_height_in_full_domain ⟨ht.1.le,ht.2.le⟩
  obtain ⟨unit,vzero⟩ := verticalA_spec dom
  have hzero : thetaHorizontalPeriod t (verticalA t)=0 :=
    (originalPeriodAlong_eq_actual dom).symm.trans hz
  let p : ClosedPeriodParameters := ⟨t,verticalA t,dom.1,unit,vzero,hzero⟩
  refine ⟨p,ht,ha,?_⟩
  intro c hc
  exact ⟨(original_all_generators_close_iff dom.1 ⟨unit.1,by linarith [unit.2]⟩ hc).mpr ⟨vzero,hzero⟩,
    actual_closed_immersion_properties p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compact_root_attachment_reconstructs_immersion

