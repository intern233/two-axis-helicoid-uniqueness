import TwoAxisHelicoid.PlaneCapSphericalTail
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

namespace TwoAxisHelicoid
open Real Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

theorem prod_norm_sq_le_sum_sq (p : ℝ × ℝ) : ‖p‖^2 ≤ p.1^2+p.2^2 := by
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  rcases le_total |p.1| |p.2| with h | h
  · rw [max_eq_right h,sq_abs]
    nlinarith [sq_nonneg p.1]
  · rw [max_eq_left h,sq_abs]
    nlinarith [sq_nonneg p.2]

theorem ambient_norm_sq_le_radius (y : HelicoidTubeCoordinates) : ‖y‖^2 ≤ ambientRadiusSq y := by
  have hp := prod_norm_sq_le_sum_sq y.1
  rw [Prod.norm_def]
  rcases le_total ‖y.1‖ ‖y.2‖ with h | h
  · rw [max_eq_right h,Real.norm_eq_abs,sq_abs]
    dsimp [ambientRadiusSq]
    nlinarith [sq_nonneg y.1.1,sq_nonneg y.1.2]
  · rw [max_eq_left h]
    dsimp [ambientRadiusSq]
    nlinarith [sq_nonneg y.2]

theorem plane_squared_radius_tendsto :
    Tendsto (fun p : ℝ × ℝ => p.1^2+p.2^2) (cobounded (ℝ × ℝ)) atTop :=
  tendsto_atTop_mono prod_norm_sq_le_sum_sq
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_norm_cobounded_atTop : Tendsto (fun p : ℝ × ℝ => ‖p‖) _ _))

theorem stereographicPlaneCap_squared_distance (H : ℝ) (p : ℝ × ℝ) :
    ambientRadiusSq (stereographicPlaneCap H p-planeCapNorth H) = H^2/(1+(p.1^2+p.2^2)) := by
  have hd : 1+(p.1^2+p.2^2) ≠ 0 := by positivity
  dsimp [ambientRadiusSq,stereographicPlaneCap,planeCapNorth]
  field_simp
  ring

theorem stereographicPlaneCap_tendsto {ι : Type*} {l : Filter ι} {p : ι → ℝ × ℝ}
    (H : ℝ) (hp : Tendsto (fun i => (p i).1^2+(p i).2^2) l atTop) :
    Tendsto (fun i => stereographicPlaneCap H (p i)) l (𝓝 (planeCapNorth H)) := by
  have hden : Tendsto (fun i => 1+((p i).1^2+(p i).2^2)) l atTop :=
    tendsto_const_nhds.add_atTop hp
  have hratio : Tendsto (fun i => H^2/(1+((p i).1^2+(p i).2^2))) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hsqrt : Tendsto (fun i => sqrt (H^2/(1+((p i).1^2+(p i).2^2)))) l (𝓝 0) := by
    simpa only [sqrt_zero] using! continuous_sqrt.continuousAt.tendsto.comp hratio
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hsqrt
  intro i
  apply (le_sqrt (norm_nonneg _) (by positivity)).mpr
  simpa only [stereographicPlaneCap_squared_distance] using
    ambient_norm_sq_le_radius (stereographicPlaneCap H (p i)-planeCapNorth H)

theorem smoothPlaneCap_tendsto {ι : Type*} {l : Filter ι} {p : ι → ℝ × ℝ}
    (A H : ℝ) (hp : Tendsto (fun i => (p i).1^2+(p i).2^2) l atTop) :
    Tendsto (fun i => smoothPlaneCap A H (p i)) l (𝓝 (planeCapNorth H)) := by
  apply (stereographicPlaneCap_tendsto H hp).congr'
  filter_upwards [hp.eventually_ge_atTop (A+1)] with i hi
  exact (smoothPlaneCap_eq_stereographic hi).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smoothPlaneCap_tendsto
