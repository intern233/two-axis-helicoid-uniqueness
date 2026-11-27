import Init

namespace TwoAxisHelicoid

/-- Adjoin uniqueness of the parameter to a geometric existence witness,
keeping every property of that same witness in the conclusion. -/
theorem exists_unique_parameter_witness {α : Type u} {P : α → Prop}
    (unique : Subsingleton α) (exists_model : ∃ p, P p) :
    ∃ p, (∀ q : α, q=p) ∧ P p :=
  exists_model.elim fun p hp => ⟨p,fun q => unique.allEq q p,hp⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_unique_parameter_witness
