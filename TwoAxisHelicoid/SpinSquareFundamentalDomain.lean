import TwoAxisHelicoid.PuncturedSquareRadial
import TwoAxisHelicoid.TorusGeneratorIntersections
import TwoAxisHelicoid.ActualTorusManifoldImmersion

namespace TwoAxisHelicoid
open Complex Set Topology

noncomputable def spinSquareLinear (L : PeriodPair) (s t : ℝ) : ℂ :=
  s • L.basis 0 + t • L.basis 1

theorem spinSquareLinear_coords (L : PeriodPair) (s t : ℝ) :
    L.basis.repr (spinSquareLinear L s t) 0 = s ∧ L.basis.repr (spinSquareLinear L s t) 1 = t := by
  simp only [spinSquareLinear,map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
    Module.Basis.repr_self_apply,smul_eq_mul]
  norm_num

theorem period_coordinates_jointly_injective (L : PeriodPair) {x y : ℂ}
    (h0 : L.basis.repr x 0 = L.basis.repr y 0) (h1 : L.basis.repr x 1 = L.basis.repr y 1) : x = y := by
  apply L.basis.repr.injective
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem integral_period_coordinates_iff (L : PeriodPair) (x : ℂ) :
    x ∈ L.lattice ↔ ∃ m n : ℤ, L.basis.repr x 0 = m ∧ L.basis.repr x 1 = n := by
  constructor
  · intro hx
    obtain ⟨m,hm⟩ := periodPair_lattice_coordinate L hx 0
    obtain ⟨n,hn⟩ := periodPair_lattice_coordinate L hx 1
    exact ⟨m,n,hm,hn⟩
  · rintro ⟨m,n,hm,hn⟩
    apply PeriodPair.mem_lattice.mpr
    refine ⟨m,n,?_⟩
    have he : spinSquareLinear L m n = x := period_coordinates_jointly_injective L
      ((spinSquareLinear_coords L _ _).1.trans hm.symm) ((spinSquareLinear_coords L _ _).2.trans hn.symm)
    simpa [spinSquareLinear,Complex.real_smul] using he

noncomputable def spinSquareLift (L : PeriodPair) (v : SpinSquare) : ℂ :=
  periodPairCenter L + spinSquareLinear L v.1 v.2

noncomputable def spinSquareTorusMap (L : PeriodPair) (v : SpinSquare) : PeriodTorus L :=
  periodTorusProjection L (spinSquareLift L v)

theorem spinSquareTorusMap_continuous (L : PeriodPair) : Continuous (spinSquareTorusMap L) := by
  apply (QuotientAddGroup.continuous_mk (N := L.lattice.toAddSubgroup)).comp
  unfold spinSquareLift spinSquareLinear
  fun_prop

theorem spinSquareTorusMap_surjective (L : PeriodPair) : Function.Surjective (spinSquareTorusMap L) := by
  intro q
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  let w := z - periodPairCenter L
  let s := L.basis.repr w 0
  let t := L.basis.repr w 1
  let u : SpinSquare := (⟨Int.fract s,Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,
    ⟨Int.fract t,Int.fract_nonneg _,(Int.fract_lt_one _).le⟩)
  refine ⟨u,QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
  apply (integral_period_coordinates_iff L _).mpr
  have hd : spinSquareLift L u - z = spinSquareLinear L (Int.fract s) (Int.fract t) - w := by
    change periodPairCenter L + _ - z = _ - (z-periodPairCenter L)
    abel
  rw [hd]
  obtain ⟨hs,ht⟩ := spinSquareLinear_coords L (Int.fract s) (Int.fract t)
  refine ⟨-⌊s⌋,-⌊t⌋,?_,?_⟩ <;> simp only [map_sub,Finsupp.sub_apply,hs,ht,Int.cast_neg]
  · change Int.fract s-s = -↑⌊s⌋
    linarith [Int.floor_add_fract s]
  · change Int.fract t-t = -↑⌊t⌋
    linarith [Int.floor_add_fract t]

theorem spinSquareTorusMap_eq_coordinates (L : PeriodPair) {u v : SpinSquare}
    (h : spinSquareTorusMap L u = spinSquareTorusMap L v) :
    (∃ m : ℤ, (u.1 : ℝ) - v.1 = m) ∧ (∃ n : ℤ, (u.2 : ℝ) - v.2 = n) := by
  have hm : spinSquareLift L u - spinSquareLift L v ∈ L.lattice := QuotientAddGroup.eq_iff_sub_mem.mp h
  obtain ⟨m,n,h0,h1⟩ := (integral_period_coordinates_iff L _).mp hm
  have hd : spinSquareLift L u-spinSquareLift L v = spinSquareLinear L u.1 u.2-spinSquareLinear L v.1 v.2 := by
    unfold spinSquareLift
    abel
  rw [hd] at h0 h1
  simp only [map_sub,Finsupp.sub_apply,(spinSquareLinear_coords L _ _).1,(spinSquareLinear_coords L _ _).2] at h0 h1
  exact ⟨⟨m,h0⟩,⟨n,h1⟩⟩

/-- In the quotient of the closed square only perimeter points are
identified. -/
theorem spinSquareTorusMap_injective_off_perimeter (L : PeriodPair) {u v : SpinSquare}
    (hu : ¬ SpinSquarePerimeter u) (h : spinSquareTorusMap L u = spinSquareTorusMap L v) : u = v := by
  have h0 : (0:ℝ) < u.1 := lt_of_le_of_ne u.1.2.1 (fun he => hu (Or.inl (Subtype.ext he.symm)))
  have h1 : (u.1:ℝ) < 1 := lt_of_le_of_ne u.1.2.2 (fun he => hu (Or.inr (Or.inl (Subtype.ext he))))
  have h2 : (0:ℝ) < u.2 := lt_of_le_of_ne u.2.2.1 (fun he => hu (Or.inr (Or.inr (Or.inl (Subtype.ext he.symm)))))
  have h3 : (u.2:ℝ) < 1 := lt_of_le_of_ne u.2.2.2 (fun he => hu (Or.inr (Or.inr (Or.inr (Subtype.ext he)))))
  obtain ⟨hx,hy⟩ := spinSquareTorusMap_eq_coordinates L h
  exact Prod.ext (Subtype.ext (sub_eq_zero.mp (real_integer_between_neg_one_one
    (by linarith [v.1.2.2]) (by linarith [v.1.2.1]) hx)))
    (Subtype.ext (sub_eq_zero.mp (real_integer_between_neg_one_one (by linarith [v.2.2.2]) (by linarith [v.2.2.1]) hy)))

noncomputable def spinSquareMidpoint : SpinSquare := (⟨1/2,by norm_num⟩,⟨1/2,by norm_num⟩)

theorem spinSquareMidpoint_maps_zero (L : PeriodPair) : spinSquareTorusMap L spinSquareMidpoint = 0 := by
  apply (periodTorusProjection_eq_zero L _).mpr
  apply PeriodPair.mem_lattice.mpr
  refine ⟨1,1,?_⟩
  simp [spinSquareLift,spinSquareMidpoint,spinSquareLinear,periodPairCenter,Complex.real_smul]
  ring

theorem spinSquareTorusMap_ne_zero_iff (L : PeriodPair) (u : SpinSquare) :
    spinSquareTorusMap L u ≠ 0 ↔ 0 < spinSquareRadius u := by
  have hmid : ¬ SpinSquarePerimeter spinSquareMidpoint := by
    simp [SpinSquarePerimeter,spinSquareMidpoint,Subtype.ext_iff]
  have hu : spinSquareTorusMap L u = 0 ↔ spinSquareRadius u = 0 := by
    constructor
    · intro h
      have heq := spinSquareTorusMap_injective_off_perimeter L hmid ((spinSquareMidpoint_maps_zero L).trans h.symm)
      subst u
      exact (spinSquareRadius_zero_iff _).mpr ⟨rfl,rfl⟩
    · intro h
      obtain ⟨hx,hy⟩ := (spinSquareRadius_zero_iff u).mp h
      have he : u = spinSquareMidpoint := Prod.ext (Subtype.ext hx) (Subtype.ext hy)
      rw [he,spinSquareMidpoint_maps_zero]
  rw [ne_eq,hu,← ne_eq,lt_iff_le_and_ne]
  exact ⟨fun h => ⟨spinSquareRadius_nonneg u,h.symm⟩,fun h => h.2.symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spinSquareTorusMap_injective_off_perimeter
#print axioms TwoAxisHelicoid.spinSquareTorusMap_ne_zero_iff
