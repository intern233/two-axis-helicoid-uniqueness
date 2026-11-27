import TwoAxisHelicoid.NullVectorRegularity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TwoAxisHelicoid
open Complex

theorem nullMetric_ge_third_normSq {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0) :
    Complex.normSq (p 2) ≤ nullMetric p := by
  have hid := complexNull_real_identities hp
  have hpos := nullMetric_pos hp hn
  have he : nullMetric p*(nullMetric p-Complex.normSq (p 2)) =
      ((p 0).re*(p 1).im-(p 1).re*(p 0).im)^2 := by
    unfold nullMetric at hid ⊢
    simp only [Complex.normSq_apply]
    linear_combination ((p 0).re^2+(p 1).re^2)*hid.1+
      ((p 0).re*(p 0).im+(p 1).re*(p 1).im-(p 2).re*(p 2).im)*hid.2
  have hnon : 0 ≤ nullMetric p*(nullMetric p-Complex.normSq (p 2)) := by
    rw [he]
    exact sq_nonneg _
  nlinarith

theorem sqrt_nullMetric_ge_third_norm {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0) :
    ‖p 2‖ ≤ Real.sqrt (nullMetric p) := by
  have h := nullMetric_ge_third_normSq hp hn
  rw [Complex.normSq_eq_norm_sq] at h
  exact (Real.le_sqrt (norm_nonneg _) (nullMetric_pos hp hn).le).mpr h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.sqrt_nullMetric_ge_third_norm
