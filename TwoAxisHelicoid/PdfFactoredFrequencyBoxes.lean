import TwoAxisHelicoid.PdfFactoredThetaAtoms
import TwoAxisHelicoid.PdfPrimalParameterBox

namespace TwoAxisHelicoid.PdfVertical

def FactoredFrequency.encloses (p q : FactoredFrequency) : Prop :=
  p.plus.encloses q.plus=true ∧ p.minus.encloses q.minus=true ∧ p.shift.encloses q.shift=true

instance FactoredFrequency.enclosesDecidable (p q : FactoredFrequency) : Decidable (p.encloses q) := by
  unfold FactoredFrequency.encloses
  infer_instance

theorem FactoredFrequency.box_sound {p : FactoredFrequency} {T A : Grid} {n : ℕ} {t a : ℝ}
    (encl : p.encloses (FactoredFrequency.build T A n)) (tl : T.Contains t) (al : A.Contains a) :
    p.Sound t a n := by
  obtain ⟨u,d,z⟩ := FactoredFrequency.build_sound tl al n
  exact ⟨Grid.contains_of_encloses u encl.1, Grid.contains_of_encloses d encl.2.1,
    CGrid.contains_of_encloses z encl.2.2⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.FactoredFrequency.box_sound

