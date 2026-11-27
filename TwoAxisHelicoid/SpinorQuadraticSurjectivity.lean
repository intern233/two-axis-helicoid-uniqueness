import TwoAxisHelicoid.SpinorQuadraticMap
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000

theorem complex_has_square_root (w : ℂ) : ∃ s : ℂ, s^2 = w := by
  by_cases hw : w = 0
  · exact ⟨0,by simp [hw]⟩
  · refine ⟨exp (log w/2),?_⟩
    rw [← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show 2*(log w/2) = log w by ring,exp_log hw]

theorem spinorQuadratic_of_squares {p : Fin 3 → ℂ} {u v : ℂ}
    (hu : u^2 = (-p 0-I*p 1)/2) (hv : v^2 = (p 0-I*p 1)/2) (huv : 2*u*v = p 2) :
    spinorQuadratic (u,v) = p := by
  ext j
  fin_cases j
  · change v^2-u^2 = p 0
    rw [hu,hv]
    ring
  · change I*(v^2+u^2) = p 1
    rw [hu,hv]
    ring_nf
    simp [I_sq]
  · exact huv

/-- Every complex null vector is the actual quadratic image of a pair
of spinors. The square roots are constructed and the zero-coordinate
case is handled explicitly. -/
theorem spinorQuadratic_surjective_null {p : Fin 3 → ℂ} (hp : ComplexNull p) :
    ∃ s : ℂ × ℂ, spinorQuadratic s = p := by
  let A := (-p 0-I*p 1)/2
  let B := (p 0-I*p 1)/2
  have hab : A*B = (p 2/2)^2 := by
    dsimp [A,B]
    ring_nf
    simp only [I_sq]
    change (p 0)^2+(p 1)^2+(p 2)^2 = 0 at hp
    linear_combination -hp/4
  by_cases hA : A = 0
  · have hp2 : p 2 = 0 := by
      have hh : (p 2)^2 = 0 := by
        rw [hA,zero_mul] at hab
        linear_combination -4*hab
      exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hh
    obtain ⟨v,hv⟩ := complex_has_square_root B
    refine ⟨(0,v),spinorQuadratic_of_squares ?_ hv ?_⟩
    · simpa using hA.symm
    · simp [hp2]
  · obtain ⟨u,hu⟩ := complex_has_square_root A
    have hu0 : u ≠ 0 := by intro hu0; apply hA; rw [← hu,hu0]; norm_num
    let v := p 2/(2*u)
    have hv : v^2 = B := by
      dsimp [v]
      field_simp
      rw [hu]
      linear_combination -4*hab
    have huv : 2*u*v = p 2 := by dsimp [v]; field_simp
    exact ⟨(u,v),spinorQuadratic_of_squares hu hv huv⟩

theorem spinorQuadratic_surjective_unit_null {p : Fin 3 → ℂ}
    (hp : ComplexNull p) (hm : nullMetric p = 1) :
    ∃ s : ℂ × ℂ, spinorWeight s = 1 ∧ spinorQuadratic s = p := by
  obtain ⟨s,hs⟩ := spinorQuadratic_surjective_null hp
  refine ⟨s,?_,hs⟩
  have hmetric := spinorQuadratic_metric s
  rw [hs,hm] at hmetric
  nlinarith [spinorWeight_nonneg s]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.spinorQuadratic_surjective_unit_null
