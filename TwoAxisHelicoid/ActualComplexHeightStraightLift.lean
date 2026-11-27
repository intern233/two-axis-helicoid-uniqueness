import TwoAxisHelicoid.ActualHeightRegularBand
import TwoAxisHelicoid.ActualComplexHeight
import TwoAxisHelicoid.SmoothFlowTransport
import TwoAxisHelicoid.UnitIntervalSlope

namespace TwoAxisHelicoid
open Complex Set

/-- Lifting any straight segment in the complex height plane whose real
parts stay away from the two saddles gives an actual path on the
lattice complement. The same bounded field works for every starting
point with this separation and the lift is unique for that field. -/
theorem actual_complex_height_straight_lift {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (period : ∀ z w, w∈(rhombicPeriodPair t ht).lattice → X (z+w)=X z) {ε : ℝ} (positive : 0<ε) :
    let L := rhombicPeriodPair t ht
    let H := actualComplexHeight t a c ht
    ∃ V : ℂ → ℂ, ContDiff ℝ 1 V ∧ (∀ z w, w∈L.lattice → V (z+w)=V z) ∧ (∀ p∈L.lattice,V p=0) ∧
      ∀ (p b : ℂ), p∉L.lattice →
        (∀ k∈Icc (0:ℝ) 1, ε≤|X p 2-X 1 2+k*b.re|) →
        ∃ γ : ℝ → ℂ, γ 0=p ∧
          (∀ s∈Icc (0:ℝ) 1, HasDerivAt γ (b*V (γ s)) s) ∧
          ∀ s∈Icc (0:ℝ) 1, γ s∉L.lattice ∧ H (γ s)=H p+s • b ∧
            X (γ s) 2=X p 2+s*b.re := by
  let L := rhombicPeriodPair t ht
  let H := actualComplexHeight t a c ht
  let f := fun z => coordinateData t a c ht z 2
  obtain ⟨δ,hδ,V,smooth,bound,per,fixed,exactOn,factor⟩ :=
    actual_height_regular_band_field ht ha hc diff period positive
  refine ⟨V,smooth,per,fixed,?_⟩
  intro p b hp sep
  let W := fun z => b*V z
  have sm : ContDiff ℝ 1 W := contDiff_const.mul smooth
  obtain ⟨γ,initial,ode⟩ := bounded_smooth_vector_field_unit_solution sm
    (show 0≤‖b‖*(δ/2)⁻¹ by positivity) (fun z => by
      change ‖b*V z‖≤_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (bound z) (norm_nonneg _)) p
  have off := smooth_field_trajectory_avoids_fixed sm ode (S := (L.lattice : Set ℂ))
    (fun z hz => by simp [W,fixed z hz]) (initial ▸ hp)
  let u := fun s => X (γ s) 2
  have du (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      HasDerivAt u ((b*V (γ s))*f (γ s)).re s :=
    (actual_coordinate_primitive_component ht diff (off s hs) 2).comp_hasDerivAt s (ode s hs)
  have ratio (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      ∃ k∈Icc (0:ℝ) 1, HasDerivAt u (k*b.re) s := by
    obtain ⟨k,hk,eq⟩ := factor _ (off s hs)
    have h := du s hs
    rw [mul_assoc,show V (γ s)*f (γ s)=(k:ℂ) from eq,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,mul_comm] at h
    exact ⟨k,hk,h⟩
  have scalar (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : V (γ s)*f (γ s)=1 := by
    obtain ⟨k,hk,h⟩ := unit_derivative_segment ratio hs
    have start : u 0=X p 2 := congrArg (fun z => X z 2) initial
    have away : ε≤|X (γ s) 2-X 1 2| := by
      change ε≤|u s-X 1 2|
      rw [h,start,show X p 2+k*b.re-X 1 2=X p 2-X 1 2+k*b.re by ring]
      exact sep k hk
    obtain ⟨large,recip⟩ := exactOn _ (off s hs) away
    have nz : f (γ s)≠0 := norm_pos_iff.mp (hδ.trans_le large)
    exact (congrArg (fun q => q*f (γ s)) recip).trans (inv_mul_cancel₀ nz)
  have dH (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt (H ∘ γ) b s := by
    have d := ((actualComplexHeight_hasDerivAt (a := a) (c := c) ht (off s hs)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s (ode s hs)
    change HasDerivAt (H ∘ γ) ((b*V (γ s))*f (γ s)) s at d
    simpa only [mul_assoc,scalar s hs,mul_one] using d
  refine ⟨γ,initial,ode,?_⟩
  intro s hs
  have hcplx := unit_constant_vector_derivative dH s hs
  change H (γ s)=H (γ 0)+s • b at hcplx
  rw [initial] at hcplx
  obtain ⟨B,hB⟩ := actual_complex_height_real_primitive ht diff
  refine ⟨off s hs,hcplx,?_⟩
  rw [hB _ (off s hs),hB p hp,show actualComplexHeight t a c ht (γ s)=H p+s • b from hcplx,Complex.add_re,Complex.smul_re]
  change (H p).re+s*b.re+B=(H p).re+B+s*b.re
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_complex_height_straight_lift
