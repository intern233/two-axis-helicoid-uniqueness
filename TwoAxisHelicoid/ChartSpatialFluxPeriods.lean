import TwoAxisHelicoid.ChartWeierstrassData
import TwoAxisHelicoid.SpatialConormalFlux

namespace TwoAxisHelicoid
open Complex Set Metric
open HolomorphicCoefficientDisks

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The oriented conormal arclength integral around a finite sequence
of genuine straight chart segments. The spatial velocity and unit
conormal come from the given immersion in each coordinate disk. -/
noncomputable def HolomorphicCoefficientDisks.AvoidingPath.spatialConormal
    {A : HolomorphicCoefficientDisks M} {U : Set M} {x y : M}
    (c : A.AvoidingPath U x y) (X : M → Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  match c with
  | .refl _ _ => 0
  | .step p x y _ _ _ =>
    let F := X ∘ (chartAt ℂ p).symm
    let v := chartAt ℂ p y-chartAt ℂ p x
    ∫ s : ℝ in 0..1, ‖fderiv ℝ (coordinateToEuclidean ∘ F) (chartSegment p x y s) v‖ *
      chartRightUnitConormal F (chartSegment p x y s) v j
  | .trans c d => c.spatialConormal X j+d.spatialConormal X j

namespace ChartWeierstrassData
variable {U : Set M} (X : ChartWeierstrassData M U)

noncomputable abbrev componentForm (j : Fin 3) (p : M) (z : ℂ) : ℂ :=
  weierstrassTriple (X.gauss ((chartAt ℂ p).symm z)) (X.height p z) j

private theorem componentForm_continuousAt (j : Fin 3) (p : M) {z : ℂ}
    (hz : z ∈ (chartAt ℂ p).target) (hu : (chartAt ℂ p).symm z ∈ U) :
    ContinuousAt (X.componentForm j p) z := by
  have hg := (X.gauss_analytic p z hz hu).continuousAt
  have hh := X.height_continuous p z hz hu
  have hgi := hg.inv₀ (X.gauss_ne_zero _ hu)
  fin_cases j
  · exact ((hgi.sub hg).div_const 2).mul hh
  · exact ((continuousAt_const.mul (hgi.add hg)).div_const 2).mul hh
  · exact hh

private theorem triple_null {g : ℂ} (hg : g ≠ 0) (h : ℂ) : ComplexNull (weierstrassTriple g h) := by
  change ((g⁻¹-g)/2*h)^2+(I*(g⁻¹+g)/2*h)^2+h^2 = 0
  linear_combination ((g⁻¹+g)^2*h^2/4)*I_sq - h^2*(inv_mul_cancel₀ hg)

theorem spatialConormal_eq_im {A : HolomorphicCoefficientDisks M} {x y : M}
    (c : A.AvoidingPath U x y) (j : Fin 3) :
    c.spatialConormal X.position j = (c.integral (X.componentForm j)).im := by
  induction c with
  | refl => rfl
  | trans c d hc hd => exact congrArg₂ (·+·) hc hd
  | step p x y hx hy hU =>
    let v := chartAt ℂ p y-chartAt ℂ p x
    have hv := segment_coefficient_integrable
      (fun p z hz hu => X.componentForm_continuousAt j p (A.ball_target p hz) hu) p hx hy hU
    have hi : (∫ s : ℝ in 0..1, v*X.componentForm j p (chartSegment p x y s)).im =
        ∫ s : ℝ in 0..1, (v*X.componentForm j p (chartSegment p x y s)).im :=
      (Complex.imCLM.intervalIntegral_comp_comm hv).symm
    rw [AvoidingPath.integral,hi]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
    have ht := A.ball_target p (A.chartSegment_mem p hx hy hs')
    exact chartRightUnitConormal_density (triple_null (X.gauss_ne_zero _ (hU s hs')) _)
      (X.differential p _ ht (hU s hs')) v j

/-- The manuscript's horizontal vector `(-Im A, Re A)` is the actual
spatial conormal integral on an arbitrary marked complex curve. -/
theorem horizontal_spatial_flux_formula {A : HolomorphicCoefficientDisks M} {x : M}
    (c : A.AvoidingPath U x x) :
    (c.spatialConormal X.position 0,c.spatialConormal X.position 1) =
      (-(c.integral (weightedGaussCoefficient X.gauss X.height)).im,
        (c.integral (weightedGaussCoefficient X.gauss X.height)).re) := by
  let f := X.componentForm 0
  let g := X.componentForm 1
  have h (j : Fin 3) (p : M) (z : ℂ) (hz : z ∈ ball (chartAt ℂ p p) (A.radius p))
      (hu : (chartAt ℂ p).symm z ∈ U) := X.componentForm_continuousAt j p (A.ball_target p hz) hu
  have hzero (j : Fin 3) : (c.integral (X.componentForm j)).re = 0 := by
    have e := c.scalar_real_integral (H := fun q => X.position q j) (h j) (fun p z hz hu =>
      (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (X.differential p z (A.ball_target p hz) hu))
    simpa using e
  have he : c.integral (weightedGaussCoefficient X.gauss X.height) = -(c.integral f+I*c.integral g) := by
    calc
      _ = c.integral (fun p z => (-1:ℂ)*(f p z+I*g p z)) := by
        apply c.integral_congr
        intro p z _ _
        dsimp [f,g,componentForm,weightedGaussCoefficient,weierstrassTriple]
        linear_combination ((X.gauss ((chartAt ℂ p).symm z))⁻¹+X.gauss ((chartAt ℂ p).symm z))*
          X.height p z / 2 * I_sq
      _ = _ := by
        rw [c.integral_const_mul,c.integral_add (F := f) (G := fun p z => I*g p z)
          (h 0) (fun p z hz hu => continuousAt_const.mul (h 1 p z hz hu)),
          c.integral_const_mul,neg_one_mul]
  rw [X.spatialConormal_eq_im,X.spatialConormal_eq_im,he]
  simp [f,g,Complex.mul_re,Complex.mul_im,hzero]

/-- A nonvertical physical flux supplies the nonzero period used by the
arbitrary-chart fixed-data and fixed-principal-part rigidity theorems. -/
theorem weighted_period_ne_zero_of_spatial_flux {A : HolomorphicCoefficientDisks M} {x : M}
    (c : A.AvoidingPath U x x) (h : c.spatialConormal X.position 0 ≠ 0 ∨ c.spatialConormal X.position 1 ≠ 0) :
    c.integral (weightedGaussCoefficient X.gauss X.height) ≠ 0 := by
  intro hz
  have e := X.horizontal_spatial_flux_formula c
  rw [hz] at e
  rcases h with h | h
  · exact h (by simpa using congrArg Prod.fst e)
  · exact h (by simpa using congrArg Prod.snd e)

end ChartWeierstrassData
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ChartWeierstrassData.horizontal_spatial_flux_formula
