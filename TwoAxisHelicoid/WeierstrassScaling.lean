import TwoAxisHelicoid.RhombicLattice

namespace TwoAxisHelicoid
open Complex

theorem weierstrassP_equiv_scale (L M : PeriodPair) (c : ℂ)
    (e : L.lattice ≃ M.lattice) (he : ∀ l : L.lattice, (e l : ℂ) = c*(l : ℂ)) (z : ℂ) :
    M.weierstrassP (c*z) = (c^2)⁻¹*L.weierstrassP z := by
  unfold PeriodPair.weierstrassP
  rw [← e.tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro l
  rw [he, ← mul_sub]
  simp only [one_div, mul_pow, mul_inv_rev]
  ring

theorem rhombic_reciprocal_factor {t : ℝ} (ht : 0 < t) (m n : ℤ) :
    (I*t)*((m : ℂ)*2+(n : ℂ)*(1+I*((1/t : ℝ) : ℂ))) =
      ((-m-n : ℤ) : ℂ)*2+((2*m+n : ℤ) : ℂ)*(1+I*t) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  ring_nf
  simp only [I_sq]
  ring

theorem rhombic_reciprocal_mem_iff {t : ℝ} (ht : 0 < t) (z : ℂ) :
    z ∈ (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).lattice ↔
      (I*t)*z ∈ (rhombicPeriodPair t ht).lattice := by
  have hc : (I*t : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  constructor
  · intro hz
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hz
    apply PeriodPair.mem_lattice.mpr
    refine ⟨-m-n,2*m+n,?_⟩
    rw [← he]
    exact (rhombic_reciprocal_factor ht m n).symm
  · intro hz
    obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hz
    apply PeriodPair.mem_lattice.mpr
    refine ⟨m+n,-2*m-n,?_⟩
    apply mul_left_cancel₀ hc
    change (I*t)*(((m+n : ℤ) : ℂ)*2+((-2*m-n : ℤ) : ℂ)*(1+I*((1/t : ℝ) : ℂ))) = (I*t)*z
    rw [rhombic_reciprocal_factor ht]
    convert he using 1
    simp only [rhombicPeriodPair]
    push_cast
    ring

noncomputable def rhombicReciprocalEquiv (t : ℝ) (ht : 0 < t) :
    (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).lattice ≃ (rhombicPeriodPair t ht).lattice where
  toFun z := ⟨(I*t)*(z : ℂ),(rhombic_reciprocal_mem_iff ht z).mp z.property⟩
  invFun z := ⟨(z : ℂ)/(I*t),(rhombic_reciprocal_mem_iff ht _).mpr (by
    have hc : (I*t : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
    have he : (I*t)*((z : ℂ)/(I*t)) = (z : ℂ) := by field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
    rw [he]
    exact z.property)⟩
  left_inv z := by
    apply Subtype.ext
    have hc : (I*t : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
    dsimp
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  right_inv z := by
    apply Subtype.ext
    have hc : (I*t : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
    dsimp
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

theorem rhombic_weierstrassP_reciprocal {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (rhombicPeriodPair t ht).weierstrassP z =
      -(1/((t : ℂ)^2))*(rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).weierstrassP (z/(I*t)) := by
  have hc : (I*t : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  have h := weierstrassP_equiv_scale (rhombicPeriodPair (1/t) (one_div_pos.mpr ht))
    (rhombicPeriodPair t ht) (I*t) (rhombicReciprocalEquiv t ht) (fun _ => rfl) (z/(I*t))
  have hz : (I*t)*(z/(I*t)) = z := by field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  rw [hz] at h
  rw [h]
  congr 1
  simp [mul_pow, I_sq]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_weierstrassP_reciprocal
