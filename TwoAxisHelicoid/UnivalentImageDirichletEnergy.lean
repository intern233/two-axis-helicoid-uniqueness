import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace TwoAxisHelicoid
open Set MeasureTheory Metric Bornology Filter Complex
open scoped Topology

/-- Real area Jacobian of a holomorphic coordinate at a regular or
critical point. -/
theorem holomorphic_real_jacobian {f : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ f z) :
    (fderiv ℝ f z).det=‖deriv f z‖^2 := by
  have hd := h.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  rw [hd.fderiv]
  change LinearMap.det ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).toLinearMap.restrictScalars ℝ)=_
  rw [LinearMap.det_restrictScalars]
  change Algebra.norm ℝ ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).det)=_
  rw [ContinuousLinearMap.det_toSpanSingleton,Algebra.norm_complex_eq]
  exact Complex.normSq_eq_norm_sq _

/-- The Dirichlet density of an injective holomorphic map with bounded
image is integrable on its whole open domain, even at irregular
boundary points. The proof uses the real change of variables formula. -/
theorem bounded_image_univalent_energy {U : Set ℂ} (op : IsOpen U) {f : ℂ → ℂ}
    (hol : DifferentiableOn ℂ f U) (inj : InjOn f U) (bounded : IsBounded (f '' U)) :
    IntegrableOn (fun z => ‖deriv f z‖^2) U := by
  have df (z : ℂ) (hz : z∈U) : DifferentiableAt ℂ f z := (hol z hz).differentiableAt (op.mem_nhds hz)
  have area := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume op.measurableSet
    (fun z hz => ((df z hz).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) inj (fun _ : ℂ => (1:ℝ))).mp
    (integrableOn_const bounded.measure_lt_top.ne)
  apply area.congr_fun ?_ op.measurableSet
  intro z hz
  change |(fderiv ℝ f z).det| * 1=‖deriv f z‖^2
  rw [holomorphic_real_jacobian (df z hz),abs_of_nonneg (sq_nonneg _),mul_one]

/-- An integrable nonnegative density on positive radii has arbitrarily
small values of radius times density, on every prescribed full-measure
set. Otherwise the nonintegrable logarithmic density would be dominated. -/
theorem arbitrarily_small_radius_times_integrable {b : ℝ} (bp : 0<b) {E : ℝ → ℝ}
    (integ : IntegrableOn E (Ioo 0 b)) {P : ℝ → Prop} (good : ∀ᵐ r ∂volume.restrict (Ioo 0 b), P r)
    {δ η : ℝ} (dp : 0<δ) (ep : 0<η) :
    ∃ r : ℝ, r∈Ioo 0 (min δ b) ∧ P r ∧ r*E r<η := by
  let c := min δ b
  have cp : 0<c := lt_min dp bp
  have sub : Ioo (0:ℝ) c⊆Ioo 0 b := Ioo_subset_Ioo_right (min_le_right _ _)
  by_contra no
  have fail (r : ℝ) (hr : r∈Ioo 0 c) (pr : P r) : η≤r*E r :=
    le_of_not_gt (fun h => no ⟨r,hr,pr,h⟩)
  have inv : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo 0 c) := by
    refine ((integ.mono_set sub).div_const η).mono' measurable_inv.aestronglyMeasurable ?_
    have gg := ae_mono (Measure.restrict_mono_set (μ:=volume) sub) good
    filter_upwards [gg,ae_restrict_mem measurableSet_Ioo] with r pr hr
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr.1)]
    apply (le_div_iff₀ ep).mpr
    calc r⁻¹*η = η/r := by ring
         _ ≤ E r := (div_le_iff₀ hr.1).mpr ((fail r hr pr).trans_eq (mul_comm _ _))
  have pow : IntegrableOn (fun r : ℝ => r^(-1:ℝ)) (Ioo 0 c) := by simpa only [Real.rpow_neg_one] using inv
  exact (lt_irrefl (-1:ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff cp).mp pow)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_image_univalent_energy
#print axioms TwoAxisHelicoid.arbitrarily_small_radius_times_integrable
