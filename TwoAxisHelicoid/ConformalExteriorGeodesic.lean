import TwoAxisHelicoid.ConformalGeodesicCutoff

namespace TwoAxisHelicoid
open Complex Real Set Metric
open scoped Topology
set_option maxHeartbeats 1000000

theorem unitVelocityBump_speed_bound (v : ℂ) : ‖unitVelocityBump v • v‖ ≤ 2 := by
  by_cases hv : 2 ≤ ‖v‖
  · have hb : unitVelocityBump v = 0 := unitVelocityBump.zero_of_le_dist
      (by simpa [unitVelocityBump,dist_zero_right] using hv)
    simp only [hb,zero_smul,norm_zero]
    norm_num
  · have h0 : 0 ≤ unitVelocityBump v := unitVelocityBump.nonneg
    have h1 : unitVelocityBump v ≤ 1 := unitVelocityBump.le_one
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg h0]
    nlinarith [norm_nonneg v,lt_of_not_ge hv]

/-- The conformal metric and its connection need only be correct outside
a disk. The bounded ODE cannot reach that disk in unit time from a point
two units farther out; energy conservation then removes the cutoff. -/
theorem exterior_conformal_metric_unit_geodesic
    {φ : ℂ → ℝ} {Γ : ℂ → ℂ} {R L : ℝ}
    (hφ : ∀ z : ℂ, R < ‖z‖ → DifferentiableAt ℝ φ z)
    (hφ0 : ∀ z : ℂ, R < ‖z‖ → 0 ≤ φ z)
    (hΓ : ContDiff ℝ 1 Γ)
    (hconn : ∀ z : ℂ, R < ‖z‖ → ∀ w : ℂ, fderiv ℝ φ z w = (Γ z*w).re)
    (hL : 0 ≤ L) (hbound : ∀ z, ‖Γ z‖ ≤ L)
    (z₀ v₀ : ℂ) (hfar : R+2 < ‖z₀‖) (hunit : conformalKineticEnergy φ z₀ v₀ = 1) :
    ∃ z v : ℝ → ℂ, z 0 = z₀ ∧ v 0 = v₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        R < ‖z t‖ ∧ HasDerivAt z (v t) t ∧ HasDerivAt v (-(Γ (z t)*(v t)^2)) t ∧
        conformalKineticEnergy φ (z t) (v t) = 1 ∧ ‖v t‖ ≤ 1 := by
  obtain ⟨γ,hγ0,hγ⟩ := bounded_smooth_vector_field_unit_solution
    (cutOffConformalGeodesicField_contDiff hΓ) (by positivity : 0 ≤ 4*L+2)
    (cutOffConformalGeodesicField_bound hL hbound) (z₀,v₀)
  have hγz t (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => (γ s).1) (unitVelocityBump (γ t).2 • (γ t).2) t := (hγ t ht).fst
  have hγv t (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => (γ s).2)
        (-(unitVelocityBump (γ t).2 : ℂ)*Γ (γ t).1*(γ t).2^2) t := (hγ t ht).snd
  have hstay t (ht : t ∈ Icc (0 : ℝ) 1) : R < ‖(γ t).1‖ := by
    have hd := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (hγz s hs).hasDerivWithinAt)
      (fun s _ => unitVelocityBump_speed_bound (γ s).2) t ht
    change ‖(γ t).1-(γ 0).1‖ ≤ 2*(t-0) at hd
    rw [hγ0] at hd
    have hnorm : ‖z₀‖ ≤ ‖(γ t).1‖+‖(γ t).1-z₀‖ := by
      calc
        ‖z₀‖ = ‖(γ t).1-((γ t).1-z₀)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith [ht.2]
  have he := conformal_geodesic_energy_constant
    (φ := φ) (Γ := Γ) (z := fun t => (γ t).1) (v := fun t => (γ t).2)
    (χ := fun t => unitVelocityBump (γ t).2)
    (fun t ht => hφ _ (hstay t ht)) (fun t ht => hconn _ (hstay t ht))
    hγz hγv
  refine ⟨fun t => (γ t).1,fun t => (γ t).2,
    congrArg Prod.fst hγ0,congrArg Prod.snd hγ0,?_⟩
  intro t ht
  have hE : conformalKineticEnergy φ (γ t).1 (γ t).2 = 1 := by
    rw [he t ht,hγ0]
    exact hunit
  have hv := conformal_unit_energy_velocity_bound (hφ0 _ (hstay t ht)) hE
  have hχ : unitVelocityBump (γ t).2 = 1 :=
    unitVelocityBump.one_of_mem_closedBall (by simpa [unitVelocityBump,dist_zero_right] using hv)
  refine ⟨hstay t ht,?_,?_,hE,hv⟩
  · simpa only [hχ,one_smul] using hγz t ht
  · simpa only [hχ,Complex.ofReal_one,neg_mul,one_mul] using hγv t ht

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exterior_conformal_metric_unit_geodesic
