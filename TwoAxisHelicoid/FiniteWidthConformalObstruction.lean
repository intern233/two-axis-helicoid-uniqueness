import TwoAxisHelicoid.FiniteWidthEscape
import TwoAxisHelicoid.CuspAreaDistortion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace TwoAxisHelicoid
open Real Complex MeasureTheory Set Filter
open scoped Topology

/-- A rectangular sector in logarithmic annulus coordinates. -/
def openComplexUnitSquare : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1)

/-- In a finite-width sector, an injective bounded-distortion chart
in the exterior plane cannot take every horizontal ray to infinity.
The area estimate and one-dimensional length obstruction apply to
the same ray by Fubini. -/
theorem no_finite_width_escaping_plane_chart {F : ℂ → ℂ}
    (diff : ∀ p ∈ openComplexUnitSquare, DifferentiableAt ℝ F p)
    (inj : InjOn F openComplexUnitSquare)
    (outside : ∀ p ∈ openComplexUnitSquare, 2 < ‖F p‖)
    {K : ℝ} (distort : ∀ p ∈ openComplexUnitSquare, ‖fderiv ℝ F p 1‖^2 ≤ K*|(fderiv ℝ F p).det|)
    (escape : ∀ y ∈ Ioo (0:ℝ) 1, Tendsto (fun x : ℝ => ‖F ⟨x,y⟩‖) (𝓝[<] 1) atTop) :
    False := by
  let i := Ioo (0:ℝ) 1
  let speed := fun p : ℂ => exteriorCuspDensity ‖F p‖ * ‖fderiv ℝ F p 1‖
  have hm : MeasurableSet openComplexUnitSquare :=
    Complex.measurableEquivRealProd.measurable (measurableSet_Ioo.prod measurableSet_Ioo)
  have hvol : volume openComplexUnitSquare ≠ ⊤ := by
    unfold openComplexUnitSquare
    rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet,
      Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ioo]
    norm_num
  have h := integrable_cusp_horizontal_speed hm hvol diff inj outside distort
  have prodInt : Integrable (fun p : ℝ × ℝ => speed ⟨p.1,p.2⟩)
      ((volume.restrict i).prod (volume.restrict i)) := by
    have hh := (Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
      Complex.measurableEquivRealProd.symm.measurableEmbedding |>.mpr h
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact hh
  have pos : volume i ≠ 0 := by simp [i,Real.volume_Ioo]
  obtain ⟨y,hy,hi⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae pos prodInt.prod_left_ae
  let γ := fun t : ℝ => F ⟨t,y⟩
  have ray (t : ℝ) : HasDerivAt (fun x : ℝ => (⟨x,y⟩ : ℂ)) 1 t := by
    have e : (fun x : ℝ => (⟨x,y⟩ : ℂ)) = fun x : ℝ => (x:ℂ)+(y:ℂ)*I := by
      funext x
      apply Complex.ext <;> simp
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((y:ℂ)*I)
  have chain (t : ℝ) (ht : t ∈ i) : HasDerivAt γ (fderiv ℝ F ⟨t,y⟩ 1) t :=
    (diff ⟨t,y⟩ ⟨ht,hy⟩).hasFDerivAt.comp_hasDerivAt t (ray t)
  apply escaping_curve_cusp_speed_not_integrable (fun t ht => (chain t ht).differentiableAt)
    (fun t ht => outside ⟨t,y⟩ ⟨ht,hy⟩) (escape y hy)
  apply hi.congr
  filter_upwards [ae_restrict_mem (μ := volume) (s := i) measurableSet_Ioo] with t ht
  rw [(chain t ht).deriv]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.no_finite_width_escaping_plane_chart
