module

public import Init

public section

namespace TwoAxisHelicoid

/-- Keep every property of an existing distinguished witness while
identifying the witnesses attached to all members of a marked family. -/
theorem unique_witness_with_all_markings {α : Type u} {β : Type v}
    {P : α → Prop} {M : β → α → Prop}
    (model : ∃ p, (∀ q : α, q=p) ∧ P p)
    (marks : ∀ s : β, ∃ p, M s p) :
    ∃ p, (∀ q : α, q=p) ∧ (∀ s, M s p) ∧ P p :=
  model.elim fun p hp =>
    ⟨p,hp.1,fun s => (marks s).elim fun q hq => hp.1 q ▸ hq,hp.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unique_witness_with_all_markings
