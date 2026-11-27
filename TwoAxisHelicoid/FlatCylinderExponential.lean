import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The exponential quotient of the horizontal periodic strip with
half-width c and period 2πs. -/
noncomputable def horizontalCylinderMap (s : ℝ) (w : ℂ) := Complex.exp (I*w/(s:ℂ))

theorem horizontalCylinderMap_norm {s : ℝ} (_hs : 0<s) (w : ℂ) :
    ‖horizontalCylinderMap s w‖=Real.exp (-w.im/s) := by
  rw [horizontalCylinderMap,Complex.norm_exp]
  congr 1
  rw [Complex.div_ofReal_re,Complex.mul_re]
  simp

theorem horizontalCylinderMap_range {s c : ℝ} (hs : 0<s) (_hc : 0<c) :
    horizontalCylinderMap s '' {w : ℂ | |w.im|<c}={z : ℂ | Real.exp (-c/s)<‖z‖ ∧ ‖z‖<Real.exp (c/s)} := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change Real.exp (-c/s)<‖horizontalCylinderMap s w‖ ∧ ‖horizontalCylinderMap s w‖<Real.exp (c/s)
    rw [horizontalCylinderMap_norm hs]
    have v := abs_lt.mp (show |w.im|<c from hw)
    exact ⟨Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (by linarith) hs),Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (by linarith) hs)⟩
  · rintro ⟨lo,hi⟩
    have nz := norm_pos_iff.mp ((Real.exp_pos _).trans lo)
    have l : -c/s<Real.log ‖z‖ := (Real.lt_log_iff_exp_lt (norm_pos_iff.mpr nz)).mpr lo
    have u : Real.log ‖z‖<c/s := (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr nz)).mpr hi
    let w := -(s:ℂ)*I*Complex.log z
    have im : w.im= -s*Real.log ‖z‖ := by simp [w,Complex.mul_im,Complex.mul_re,Complex.log_re]
    refine ⟨w,?_,?_⟩
    · change |w.im|<c
      rw [im]
      have g := (div_lt_iff₀ hs).mp l
      have h := (lt_div_iff₀ hs).mp u
      exact abs_lt.mpr ⟨by nlinarith,by nlinarith⟩
    · apply (congrArg Complex.exp _).trans (Complex.exp_log nz)
      rw [div_eq_iff (Complex.ofReal_ne_zero.mpr hs.ne')]
      dsimp [w]
      linear_combination -(s:ℂ)*Complex.log z*Complex.I_sq

theorem horizontalCylinderMap_fibers {s : ℝ} (hs : 0<s) (v w : ℂ) :
    horizontalCylinderMap s v=horizontalCylinderMap s w ↔ ∃ n : ℤ, v=w+(n:ℂ)*(2*(Real.pi:ℂ)*(s:ℂ)) := by
  have nz := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [horizontalCylinderMap,horizontalCylinderMap,Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n,e⟩
    refine ⟨n,?_⟩
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      I*v = (I*v/(s:ℂ))*(s:ℂ) := (div_mul_cancel₀ _ nz).symm
      _ = _ := by rw [e,add_mul,div_mul_cancel₀ _ nz]; ring
  · rintro ⟨n,rfl⟩
    refine ⟨n,?_⟩
    field_simp

/-- Imaginary translations of a right half-plane have punctured disk
quotient; for vertical period 2πs the quotient is exp(-w/s). -/
noncomputable def verticalCylinderMap (s : ℝ) (w : ℂ) := Complex.exp (-w/(s:ℂ))

theorem verticalCylinderMap_range {s : ℝ} (hs : 0<s) :
    verticalCylinderMap s '' {w : ℂ | 0<w.re}={z : ℂ | 0<‖z‖ ∧ ‖z‖<1} := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change 0<‖Complex.exp (-w/(s:ℂ))‖ ∧ ‖Complex.exp (-w/(s:ℂ))‖<1
    rw [Complex.norm_exp,Complex.div_ofReal_re,Complex.neg_re]
    exact ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos hw) hs)⟩
  · rintro ⟨nz,small⟩
    let w := -(s:ℂ)*Complex.log z
    refine ⟨w,?_,?_⟩
    · change 0<w.re
      simp [w,Complex.mul_re,Complex.log_re]
      nlinarith [mul_neg_of_pos_of_neg hs (Real.log_neg nz small)]
    · change Complex.exp (-(-(s:ℂ)*Complex.log z)/(s:ℂ))=z
      rw [neg_mul,neg_neg,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hs.ne'),Complex.exp_log (norm_pos_iff.mp nz)]

theorem verticalCylinderMap_fibers {s : ℝ} (hs : 0<s) (v w : ℂ) :
    verticalCylinderMap s v=verticalCylinderMap s w ↔ ∃ n : ℤ, v=w+(n:ℂ)*(2*(Real.pi:ℂ)*(s:ℂ)*I) := by
  have nz := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [verticalCylinderMap,verticalCylinderMap,Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n,e⟩
    refine ⟨-n,?_⟩
    push_cast
    field_simp [nz] at e
    linear_combination -e
  · rintro ⟨n,rfl⟩
    refine ⟨-n,?_⟩
    push_cast
    field_simp
    ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.verticalCylinderMap_fibers
