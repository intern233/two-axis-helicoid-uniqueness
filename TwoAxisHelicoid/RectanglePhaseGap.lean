import TwoAxisHelicoid.RectangleIntermediateValue

namespace TwoAxisHelicoid
open Set Topology

/-- If no zero of height in the middle of the rectangle lies at an
integral multiple of π of the lifted phase, the constant phases on
the horizontal edges differ by at most π. The height is allowed to
vanish on both horizontal edges and at all corners. -/
theorem rectangle_phase_gap_of_no_horizontal_axis (H F : unitInterval × unitInterval → ℝ)
    (cH : Continuous H) (cF : Continuous F)
    (vertical : (∀ y, H (0,y)≤0 ∧ 0≤H (1,y)) ∨ (∀ y, 0≤H (0,y) ∧ H (1,y)≤0))
    (vl : ∀ y : unitInterval, y ≠ 0 → y ≠ 1 → H (0,y) ≠ 0 ∧ H (1,y) ≠ 0)
    (n m : ℤ) (bottom : ∀ x, F (x,0)=n*Real.pi) (top : ∀ x, F (x,1)=m*Real.pi)
    (no : ∀ q : unitInterval × unitInterval, q.1≠0 → q.1≠1 → q.2≠0 → q.2≠1 →
      H q=0 → ∀ k : ℤ, F q≠k*Real.pi) :
    |n-m|≤1 := by
  have not_between (k : ℤ) (op : (n<k ∧ k<m) ∨ (m<k ∧ k<n)) : False := by
    obtain ⟨h,ch,hl,hr,hz⟩ : ∃ h : unitInterval × unitInterval → ℝ, Continuous h ∧
        (∀ y, h (0,y)≤0) ∧ (∀ y, 0≤h (1,y)) ∧ (∀ q, h q=0 → H q=0) := by
      rcases vertical with ord | ord
      · exact ⟨H,cH,fun y => (ord y).1,fun y => (ord y).2,fun _ e => e⟩
      · exact ⟨-H,cH.neg,fun y => neg_nonpos.mpr (ord y).1,fun y => neg_nonneg.mpr (ord y).2,
          fun _ e => neg_eq_zero.mp e⟩
    obtain ⟨g,cg,gb,gt,gz⟩ : ∃ g : unitInterval × unitInterval → ℝ, Continuous g ∧
        (∀ x, g (x,0)<0) ∧ (∀ x, 0<g (x,1)) ∧ (∀ q, g q=0 → F q=k*Real.pi) := by
      rcases op with ⟨lk,ku⟩ | ⟨lk,ku⟩
      · refine ⟨fun q => F q-k*Real.pi,cF.sub continuous_const,fun x => ?_,fun x => ?_,fun _ e => sub_eq_zero.mp e⟩
        · dsimp only; rw [bottom]; exact sub_neg.mpr (mul_lt_mul_of_pos_right (by exact_mod_cast lk) Real.pi_pos)
        · dsimp only; rw [top]; exact sub_pos.mpr (mul_lt_mul_of_pos_right (by exact_mod_cast ku) Real.pi_pos)
      · refine ⟨fun q => k*Real.pi-F q,continuous_const.sub cF,fun x => ?_,fun x => ?_,fun _ e => (sub_eq_zero.mp e).symm⟩
        · dsimp only; rw [bottom]; exact sub_neg.mpr (mul_lt_mul_of_pos_right (by exact_mod_cast ku) Real.pi_pos)
        · dsimp only; rw [top]; exact sub_pos.mpr (mul_lt_mul_of_pos_right (by exact_mod_cast lk) Real.pi_pos)
    let P := fun q => Complex.mk (h q) (g q)
    have cp : Continuous P := Complex.equivRealProdCLM.symm.continuous.comp (ch.prodMk cg)
    obtain ⟨⟨x,y⟩,e⟩ := rectangle_intermediate_value_two_coordinates P cp hl hr gb gt
    have eH := hz (x,y) (congrArg Complex.re e)
    have eG : g (x,y)=0 := congrArg Complex.im e
    have y0 : y ≠ 0 := by rintro rfl; exact (gb x).ne eG
    have y1 : y ≠ 1 := by rintro rfl; exact (gt x).ne' eG
    have x0 : x ≠ 0 := by rintro rfl; exact (vl y y0 y1).1 eH
    have x1 : x ≠ 1 := by rintro rfl; exact (vl y y0 y1).2 eH
    exact no (x,y) x0 x1 y0 y1 eH k (gz _ eG)
  rw [abs_le]
  constructor
  · by_contra! h
    exact not_between (n+1) (Or.inl ⟨by omega,by omega⟩)
  · by_contra! h
    exact not_between (m+1) (Or.inr ⟨by omega,by omega⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_phase_gap_of_no_horizontal_axis
