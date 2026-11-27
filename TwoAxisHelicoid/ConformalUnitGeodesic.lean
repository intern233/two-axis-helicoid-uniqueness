import TwoAxisHelicoid.ConformalGeodesicCutoff

namespace TwoAxisHelicoid
open Complex Real Set Metric
open scoped Topology
set_option maxHeartbeats 1000000

/-- Actual unit-speed conformal geodesics are constructed by a bounded ODE.
Energy conservation removes the velocity cutoff everywhere on the segment. -/
theorem conformal_metric_unit_geodesic_segment
    {φ : ℂ → ℝ} {Γ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hφ0 : ∀ z, 0 ≤ φ z)
    (hΓ : ContDiff ℝ 1 Γ)
    (hconn : ∀ z w : ℂ, fderiv ℝ φ z w = (Γ z*w).re)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ z, ‖Γ z‖ ≤ L)
    (z₀ v₀ : ℂ) (hunit : conformalKineticEnergy φ z₀ v₀ = 1) :
    ∃ z v : ℝ → ℂ, z 0 = z₀ ∧ v 0 = v₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt z (v t) t ∧ HasDerivAt v (-(Γ (z t)*(v t)^2)) t ∧
        conformalKineticEnergy φ (z t) (v t) = 1 ∧ ‖v t‖ ≤ 1 := by
  obtain ⟨γ,hγ0,hγ⟩ := bounded_smooth_vector_field_unit_solution
    (cutOffConformalGeodesicField_contDiff hΓ) (by positivity : 0 ≤ 4*L+2)
    (cutOffConformalGeodesicField_bound hL hbound) (z₀,v₀)
  have he := conformal_geodesic_energy_constant
    (φ := φ) (Γ := Γ) (z := fun t => (γ t).1) (v := fun t => (γ t).2)
    (χ := fun t => unitVelocityBump (γ t).2)
    (fun t _ => (hφ.differentiable one_ne_zero).differentiableAt)
    (fun t _ w => hconn (γ t).1 w)
    (fun t ht => (hγ t ht).fst) (fun t ht => (hγ t ht).snd)
  refine ⟨fun t => (γ t).1,fun t => (γ t).2,
    congrArg Prod.fst hγ0,congrArg Prod.snd hγ0,?_⟩
  intro t ht
  have hE : conformalKineticEnergy φ (γ t).1 (γ t).2 = 1 := by
    rw [he t ht,hγ0]
    exact hunit
  have hv := conformal_unit_energy_velocity_bound (hφ0 (γ t).1) hE
  have hχ : unitVelocityBump (γ t).2 = 1 :=
    unitVelocityBump.one_of_mem_closedBall (by simpa [unitVelocityBump,dist_zero_right] using hv)
  refine ⟨?_,?_,hE,hv⟩
  · have hz : HasDerivAt (fun s => (γ s).1) (unitVelocityBump (γ t).2 • (γ t).2) t := (hγ t ht).fst
    simpa only [hχ,one_smul] using hz
  · have ha : HasDerivAt (fun s => (γ s).2)
      (-(unitVelocityBump (γ t).2 : ℂ)*Γ (γ t).1*(γ t).2^2) t := (hγ t ht).snd
    simpa only [hχ,Complex.ofReal_one,neg_mul,one_mul] using ha

theorem complex_unit_curve_stays_in_exterior {z v : ℝ → ℂ}
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt z (v t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, ‖v t‖ ≤ 1)
    {R : ℝ} (hR : R+1 < ‖z 0‖) :
    ∀ t ∈ Icc (0 : ℝ) 1, R < ‖z t‖ := by
  intro t ht
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hz s hs).hasDerivWithinAt)
    (fun s hs => hv s (Ico_subset_Icc_self hs)) t ht
  simp only [one_mul,sub_zero] at he
  have hnorm : ‖z 0‖ ≤ ‖z t‖+‖z t-z 0‖ := by
    calc
      ‖z 0‖ = ‖z t-(z t-z 0)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith [ht.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conformal_metric_unit_geodesic_segment
