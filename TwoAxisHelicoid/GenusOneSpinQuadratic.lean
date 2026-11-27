import TwoAxisHelicoid.AdaptedGeneratorSpinLift

namespace TwoAxisHelicoid

/-- The mod-two intersection pairing in marked symplectic coordinates. -/
def torusIntersectionModTwo (v w : ZMod 2 × ZMod 2) : ZMod 2 :=
  v.1*w.2+v.2*w.1

/-- A quadratic refinement with specified values on the marked generators. -/
def torusQuadratic (a b : ZMod 2) (v : ZMod 2 × ZMod 2) : ZMod 2 :=
  a*v.1+b*v.2+v.1*v.2

theorem torusQuadratic_polar (a b : ZMod 2) (v w : ZMod 2 × ZMod 2) :
    torusQuadratic a b (v+w) =
      torusQuadratic a b v+torusQuadratic a b w+torusIntersectionModTwo v w := by
  simp only [torusQuadratic,torusIntersectionModTwo,Prod.fst_add,Prod.snd_add]
  ring

theorem torusQuadratic_unique (f : ZMod 2 × ZMod 2 → ZMod 2)
    (h0 : f 0 = 0)
    (h : ∀ v w, f (v+w) = f v+f w+torusIntersectionModTwo v w) :
    f = torusQuadratic (f (1,0)) (f (0,1)) := by
  funext v
  rcases v with ⟨x,y⟩
  rcases zmod_two_cases x with rfl | rfl <;> rcases zmod_two_cases y with rfl | rfl
  · exact h0.trans (by simp [torusQuadratic])
  · simp [torusQuadratic]
  · simp [torusQuadratic]
  · simpa [torusQuadratic,torusIntersectionModTwo] using h (1,0) (0,1)

/-- In genus one, the product defining the Arf invariant has the same
value on every symplectic pair. -/
theorem torusQuadratic_arf_basis (a b : ZMod 2) (v w : ZMod 2 × ZMod 2)
    (h : torusIntersectionModTwo v w = 1) :
    torusQuadratic a b v*torusQuadratic a b w = a*b := by
  rcases v with ⟨x,y⟩
  rcases w with ⟨z,t⟩
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    rcases zmod_two_cases x with rfl | rfl <;> rcases zmod_two_cases y with rfl | rfl <;>
    rcases zmod_two_cases z with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl <;>
    (revert h; decide)

/-- Read the generator values of the quadratic form from the actual
tangent-adapted quaternion lifts. A closed lift represents the
nonbounding spin circle. -/
noncomputable def integerGeneratorQuadratic (m : ℤ) :=
  torusQuadratic 1 (1+(m : ZMod 2))

theorem integerGeneratorQuadratic_first {t a : ℝ} (ht : 0 < t) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    integerGeneratorQuadratic m (1,0) = 1 ↔
      adaptedWeierstrassGeneratorLift ht ha m hC 0 1 = adaptedWeierstrassGeneratorLift ht ha m hC 0 0 :=
  ⟨fun _ => (adaptedWeierstrassGeneratorLift_endpoints ht ha m hC).1,
    fun _ => by simp [integerGeneratorQuadratic,torusQuadratic]⟩

theorem integerGeneratorQuadratic_second {t a : ℝ} (ht : 0 < t) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    integerGeneratorQuadratic m (0,1) = 1 ↔
      adaptedWeierstrassGeneratorLift ht ha m hC 1 1 = adaptedWeierstrassGeneratorLift ht ha m hC 1 0 := by
  have he : adaptedWeierstrassGeneratorLift ht ha m hC 1 1 =
      adaptedWeierstrassGeneratorLift ht ha m hC 1 0 ↔ Even m := by
    rw [(adaptedWeierstrassGeneratorLift_endpoints ht ha m hC).2]
    by_cases hm : Even m <;> simp [hm,unitQuaternionAntipode_ne]
  rw [he]
  simp [integerGeneratorQuadratic,torusQuadratic,ZMod.intCast_eq_zero_iff_even]

theorem integerGeneratorQuadratic_arf_eq_section_parity {t : ℝ} (ht : 0 < t) (m : ℤ)
    {v w : ZMod 2 × ZMod 2} (h : torusIntersectionModTwo v w = 1) :
    integerGeneratorQuadratic m v*integerGeneratorQuadratic m w =
      (Module.finrank ℂ (flatHolomorphicSections t 1 ((-1 : ℂ)^m)) : ZMod 2) := by
  rw [integerSpinorSections_finrank ht m]
  change torusQuadratic _ _ v*torusQuadratic _ _ w = _
  rw [torusQuadratic_arf_basis _ _ _ _ h,one_mul]
  by_cases hm : Even m
  · simp [hm,(ZMod.intCast_eq_zero_iff_even (n := m)).mpr hm]
  · have h1 : (m : ZMod 2) = 1 := (zmod_two_cases _).resolve_left
        (fun h0 => hm ((ZMod.intCast_eq_zero_iff_even (n := m)).mp h0))
    simp [hm,h1,show (1 : ZMod 2)+1 = 0 from by decide]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torusQuadratic_arf_basis
#print axioms TwoAxisHelicoid.integerGeneratorQuadratic_arf_eq_section_parity
