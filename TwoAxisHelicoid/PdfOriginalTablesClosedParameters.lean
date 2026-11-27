import TwoAxisHelicoid.PdfRawTablesPeriodRoot
import TwoAxisHelicoid.ClosedPeriodParameters

namespace TwoAxisHelicoid.PdfVertical
open Set

/-- The original interval tables force equality of all solutions of the two
closed-period equations over their entire admissible domain. -/
theorem original_attachments_subsingleton_closed_parameters : Subsingleton ClosedPeriodParameters := by
  constructor
  intro q p
  have closes (r : ClosedPeriodParameters) :
      ∃ h : 0<(r.t,r.a).1, (r.t,r.a).2∈Ioo (0:ℝ) 1 ∧ ∀ j : Fin 3,
        (originalCoordinatePeriod r.t r.a 1 h j).re=0 ∧
        (conjugateCoordinatePeriod r.t r.a 1 h j).re=0 :=
    ⟨r.height_pos,r.abscissa_mem,(original_all_generators_close_iff r.height_pos
      ⟨r.abscissa_mem.1,by linarith [r.abscissa_mem.2]⟩ one_ne_zero).mpr
      ⟨r.vertical_closed,r.horizontal_closed⟩⟩
  have pair : (q.t,q.a)=(p.t,p.a) :=
    (original_attachments_unique_at_all_positive_heights 1 one_ne_zero).unique (closes q) (closes p)
  cases q
  cases p
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
  rfl

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_attachments_subsingleton_closed_parameters
