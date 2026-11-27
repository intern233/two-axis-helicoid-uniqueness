import TwoAxisHelicoid.UnitIntervalCover

namespace TwoAxisHelicoid

theorem right_rectangle_parameter_partition {t a : ℝ}
    (htl : (7/5 : ℝ) ≤ t) (htu : t ≤ (141/100 : ℝ))
    (hal : (9/10 : ℝ) ≤ a) (hau : a ≤ 1) :
    ∃ i : Fin 2, ∃ j : Fin 20,
      (280+(i : ℝ))/200 ≤ t ∧ t ≤ (281+(i : ℝ))/200 ∧
      (180+(j : ℝ))/200 ≤ a ∧ a ≤ (181+(j : ℝ))/200 := by
  obtain ⟨i, hil, hiu⟩ := exists_unit_subinterval (by decide : 0 < 2)
    (x := 200*t-280) (by linarith) (by norm_num; linarith)
  obtain ⟨j, hjl, hju⟩ := exists_unit_subinterval (by decide : 0 < 20)
    (x := 200*a-180) (by linarith) (by norm_num; linarith)
  exact ⟨i, j, by linarith, by linarith, by linarith, by linarith⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.right_rectangle_parameter_partition
