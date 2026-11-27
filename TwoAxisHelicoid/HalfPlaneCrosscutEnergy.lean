import TwoAxisHelicoid.UnivalentImageDirichletEnergy
import TwoAxisHelicoid.AngularDiskEnergy
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace TwoAxisHelicoid
open Set Filter MeasureTheory Metric Complex Bornology
open scoped Topology Interval

abbrev rightPlaneDomain : Set ℂ := {z | 0<z.re}

noncomputable def halfPlaneJacobian (f : ℂ → ℂ) (x y : ℝ) : ℝ :=
  rightPlaneDomain.indicator (fun z => ‖deriv f z‖^2) ⟨x,y⟩

theorem halfPlaneJacobian_nonneg (f : ℂ → ℂ) (x y : ℝ) : 0≤halfPlaneJacobian f x y :=
  indicator_nonneg (fun _ _ => sq_nonneg _) _

/-- Fubini on the plane, in real Cartesian coordinates, selects
simultaneously short vertical and horizontal traces around a boundary
point. All three squared derivative traces refer to the same radius. -/
theorem univalent_half_plane_small_energy_slices {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f rightPlaneDomain)
    (inj : InjOn f rightPlaneDomain) (bounded : IsBounded (f '' rightPlaneDomain))
    {δ η : ℝ} (dp : 0<δ) (ep : 0<η) :
    let J := halfPlaneJacobian f
    ∃ r : ℝ, 0<r ∧ r<δ ∧ Integrable (J r) ∧ Integrable (fun x => J x r) ∧ Integrable (fun x => J x (-r)) ∧
      r*((∫ y, J r y)+(∫ x, J x r)+(∫ x, J x (-r)))<η := by
  intro J
  have opened : IsOpen rightPlaneDomain := isOpen_lt continuous_const continuous_re
  have energy := bounded_image_univalent_energy opened hf inj bounded
  have plane := energy.integrable_indicator opened.measurableSet
  have product : Integrable (fun p : ℝ×ℝ => J p.1 p.2) ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable plane
  let H := fun r : ℝ => ∫ x, J x r
  let V := fun r : ℝ => ∫ y, J r y
  have hi : Integrable H := product.integral_prod_right
  have vi : Integrable V := product.integral_prod_left
  have negPres := Measure.measurePreserving_neg (volume : Measure ℝ)
  have negGood : ∀ᵐ r ∂(volume : Measure ℝ), Integrable (fun x => J x (-r)) :=
    negPres.quasiMeasurePreserving.tendsto_ae.eventually product.prod_left_ae
  have all : ∀ᵐ r ∂(volume : Measure ℝ), Integrable (J r) ∧ Integrable (fun x => J x r) ∧ Integrable (fun x => J x (-r)) := by
    filter_upwards [product.prod_right_ae,product.prod_left_ae,negGood] with r v a b using ⟨v,a,b⟩
  obtain ⟨r,hr,good,small⟩ := arbitrarily_small_radius_times_integrable (b:=1) zero_lt_one
    ((vi.add hi).add (negPres.integrable_comp_of_integrable hi)).integrableOn
    (ae_restrict_of_ae all) dp ep
  exact ⟨r,hr.1,hr.2.trans_le (min_le_left _ _),good.1,good.2.1,good.2.2,small⟩

/-- Endpoint displacement of a differentiable path is bounded by
its length in parameter time times its one-dimensional energy. -/
theorem interval_path_squared_displacement {a b : ℝ} (ab : a≤b) {f v : ℝ → ℂ}
    (cv : ContinuousOn v (Icc a b)) (df : ∀ x∈Icc a b, HasDerivAt f (v x) x) :
    dist (f b) (f a)^2≤(b-a)*(∫ x in a..b, ‖v x‖^2) := by
  rcases ab.eq_or_lt with rfl|lt
  · simp
  have vi := cv.intervalIntegrable_of_Icc (μ:=volume) lt.le
  have eq : (∫ x in a..b, v x)=f b-f a := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => df x (uIcc_of_le lt.le ▸ hx)) vi
  have dist : dist (f b) (f a)≤∫ x in a..b, ‖v x‖ := by
    rw [dist_eq_norm,← eq]
    exact intervalIntegral.norm_integral_le_integral_norm lt.le
  exact (sq_le_sq₀ dist_nonneg (dist_nonneg.trans dist)).mpr dist |>.trans (interval_integral_square_le lt cv.norm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.univalent_half_plane_small_energy_slices
#print axioms TwoAxisHelicoid.interval_path_squared_displacement
