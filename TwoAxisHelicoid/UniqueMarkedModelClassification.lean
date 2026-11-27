module

public import Init

public section

namespace TwoAxisHelicoid

/-- The two parameter bounds, the embedded models and the classification
with markings all use the witness selected by the original period tables. -/
theorem classify_unique_marked_models {Param : Type u} {Scale : Type v}
    {valid : Scale → Prop} {marked lower upper normalized placed classified : Param → Prop}
    {embedded image : Param → (c : Scale) → valid c → Prop} {geometry : Prop}
    (certified : Param)
    (root : ∃ p, (∀ q : Param, q = p) ∧ marked p ∧ lower p ∧ upper p ∧
      ∀ c hc, embedded p c hc ∧ image p c hc)
    (transport : ∀ p, marked p → normalized p ∧ placed p)
    (assemble : ∀ p, geometry → normalized p → placed p → classified p)
    (model : geometry) :
    ∃ p, p = certified ∧ (∀ q : Param, q = p) ∧ lower p ∧ upper p ∧ classified p ∧
      ∀ c hc, embedded p c hc := by
  obtain ⟨p, unique, marking, lo, hi, scales⟩ := root
  obtain ⟨n, s⟩ := transport p marking
  exact ⟨p, (unique certified).symm, unique, lo, hi, assemble p model n s,
    fun c hc => (scales c hc).1⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.classify_unique_marked_models
