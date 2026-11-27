import TwoAxisHelicoid.CoordinateDataSymmetry
import TwoAxisHelicoid.HolomorphicNullImmersion
import TwoAxisHelicoid.RhombicRegularPaths

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
attribute [local irreducible] coordinateData

theorem coordinateData_horizontal_axis {t a c : ℝ} (ht : 0 < t) (x : ℝ) :
    (coordinateData t a c ht x 1).re = 0 ∧ (coordinateData t a c ht x 2).re = 0 := by
  have h₁ := congrArg (fun p : Fin 3 → ℂ => (p 1).re) (coordinateData_conj (a := a) (c := c) ht (x : ℂ))
  have h₂ := congrArg (fun p : Fin 3 → ℂ => (p 2).re) (coordinateData_conj (a := a) (c := c) ht (x : ℂ))
  simp only [Complex.conj_ofReal] at h₁ h₂
  change (coordinateData t a c ht x 1).re = -(coordinateData t a c ht x 1).re at h₁
  change (coordinateData t a c ht x 2).re = -(coordinateData t a c ht x 2).re at h₂
  exact ⟨by linarith,by linarith⟩

theorem coordinateData_vertical_axis {t a c : ℝ} (ht : 0 < t) (y : ℝ) :
    (coordinateData t a c ht (1+I*y) 0).im = 0 ∧
      (coordinateData t a c ht (1+I*y) 1).im = 0 := by
  let z : ℂ := 1+I*y
  have he : -conj z = z+(-2) := by simp [z]; ring
  have hp : coordinateData t a c ht (-conj z) = coordinateData t a c ht z := by
    rw [he]
    exact coordinateData_add_lattice ht z
      ⟨-2,(rhombicPeriodPair t ht).lattice.neg_mem (rhombicPeriodPair t ht).ω₁_mem_lattice⟩
  have hh := coordinateData_neg (a := a) (c := c) ht (conj z)
  rw [coordinateData_conj ht,hp] at hh
  have h₀ := congrArg (fun p : Fin 3 → ℂ => (p 0).im) hh
  have h₁ := congrArg (fun p : Fin 3 → ℂ => (p 1).im) hh
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Complex.conj_im,neg_neg] at h₀ h₁
  exact ⟨by linarith,by linarith⟩

theorem rhombic_vertical_axis_not_mem {t y : ℝ} (ht : 0 < t) (hy : y ∈ Ioo (-t) t) :
    (1+I*y : ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
  intro h
  obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht _).mp h
  norm_num [Complex.mul_re,Complex.mul_im] at hr hi
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast (show (-1 : ℝ) < n by nlinarith [hy.1])
  have hnhi : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by nlinarith [hy.2])
  have hn : n = 0 := by omega
  subst n
  norm_num at hr
  have hm : (2 : ℤ)*m = 1 := by exact_mod_cast hr.symm
  omega

theorem coordinateData_horizontal_axis_regular {t a c x : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hx : x ∈ Ioo (0 : ℝ) 2) :
    (coordinateData t a c ht x 0).re ≠ 0 := by
  have hz := real_not_mem_rhombic_lattice_of_pos ht hx.1 hx.2
  have haxis := coordinateData_horizontal_axis (a := a) (c := c) ht x
  intro h
  have hpos := nullMetric_pos (p := coordinateData t a c ht x)
    (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)
  unfold nullMetric at hpos
  rw [h,haxis.1,haxis.2] at hpos
  norm_num at hpos

theorem coordinateData_vertical_axis_regular {t a c y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hy : y ∈ Ioo (-t) t) :
    (I*coordinateData t a c ht (1+I*y) 2).re ≠ 0 := by
  have hz := rhombic_vertical_axis_not_mem ht hy
  have haxis := coordinateData_vertical_axis (a := a) (c := c) ht y
  intro h
  have h₂ : (coordinateData t a c ht (1+I*y) 2).im = 0 := by simpa [Complex.mul_re] using h
  have hid := (complexNull_real_identities (p := coordinateData t a c ht (1+I*y))
    (coordinateData_null ht ha hz)).1
  have hpos := nullMetric_pos (p := coordinateData t a c ht (1+I*y))
    (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)
  rw [hid,haxis.1,haxis.2,h₂] at hpos
  norm_num at hpos

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coordinateData_horizontal_axis_regular
