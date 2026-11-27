import TwoAxisHelicoid.HalfPlaneDeckCoordinates
import TwoAxisHelicoid.RoundCylinderParameter

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology ContDiff Manifold

private theorem disk_point_norm (z : RiemannUnitDisk) : ‖z.1‖<1 := by
  simpa using (show z.1∈ball 0 1 from z.2)

private theorem disk_boundary_log_step {a b : ℝ} (pos : 0<a) (non : a≠1) {u : ℂ} (hu : ‖u‖=1)
    {x y : ℂ} (hx : ‖x‖<1)
    (step : boundaryCayley u y=(a:ℂ)*boundaryCayley u x+(b:ℂ)*I) :
    boundaryLogCoordinate u (b/(1-a)) y=boundaryLogCoordinate u (b/(1-a)) x+(Real.log a:ℂ) := by
  let q := b/(1-a)
  have qrel : q*(1-a)=b := div_mul_cancel₀ _ (sub_ne_zero.mpr non.symm)
  have cq : (q:ℂ)*(1-(a:ℂ))=(b:ℂ) := by exact_mod_cast qrel
  have eq : boundaryCayley u y-(q:ℂ)*I=(a:ℂ)*(boundaryCayley u x-(q:ℂ)*I) := by
    rw [step,← cq]
    ring
  have nz : boundaryCayley u x-(q:ℂ)*I≠0 := by
    intro zero
    have re := congrArg Complex.re zero
    simp at re
    exact (boundaryCayley_right hu hx).ne' re
  change Complex.log (boundaryCayley u y-(q:ℂ)*I)=Complex.log (boundaryCayley u x-(q:ℂ)*I)+(Real.log a:ℂ)
  rw [eq,Complex.log_ofReal_mul pos nz,add_comm]

/-- A free disk deck generator gives an explicit, everywhere unramified
analytic parameter on its orbit space. Parabolic generators give a
punctured disk and hyperbolic generators give a finite annulus. -/
theorem disk_cyclic_quotient_parameter {t : ℂ} (ht : t≠0) (e : ℂ ≃ RiemannUnitDisk)
    (f : RiemannUnitDisk ≃ₜ RiemannUnitDisk)
    (hol : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) (inv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm)
    (free : ∀ z, f z≠z) (step : ∀ z, e (z+t)=f (e z)) :
    ∃ (F : ℂ → ℂ) (T : Set ℂ), IsRoundCylinderTarget T ∧ F '' complexUnitDisk=T ∧
      (∀ z∈complexUnitDisk, AnalyticAt ℂ F z ∧ deriv F z≠0) ∧
      ∀ x y : RiemannUnitDisk, F x.1=F y.1 ↔ ∃ n : ℤ, e.symm x=e.symm y+(n:ℂ)*t := by
  obtain ⟨u,a,b,hu,ha,non,action⟩ := disk_deck_half_plane_form f hol inv free
  by_cases one : a=1
  · subst a
    obtain ⟨s,hs,sig⟩ := abs_period_scale (non.resolve_left (by simp))
    let A := fun z : RiemannUnitDisk => boundaryCayley u z.1
    have ainj : Function.Injective A := fun x y h => Subtype.ext
      ((boundaryCayley_left_inv hu (disk_point_norm x)).symm.trans
        ((congrArg (boundaryCayleyInv u) h).trans (boundaryCayley_left_inv hu (disk_point_norm y))))
    have st (z : ℂ) : A (e (z+t))=A (e z)+(b:ℂ)*I := by
      rw [step]
      simpa only [A,Complex.ofReal_one,one_mul] using action (e z)
    have per (v w : ℂ) : verticalCylinderMap s v=verticalCylinderMap s w ↔ ∃ n : ℤ, v=w+(n:ℂ)*((b:ℂ)*I) :=
      (verticalCylinderMap_fibers hs v w).trans (integer_shifts_same_up_to_sign
        (sig.elim (fun eq => Or.inl (congrArg (·*I) eq)) (fun eq => Or.inr (by rw [eq,neg_mul]))) v w)
    refine ⟨verticalCylinderMap s ∘ boundaryCayley u,_,Or.inr (Or.inl rfl),?_,?_,?_⟩
    · rw [image_comp,boundaryCayley_exact_range hu,verticalCylinderMap_range hs]
    · intro z hz
      exact analytic_regular_comp (boundaryCayley_regular hu (by simpa using (show z∈ball 0 1 from hz))) (verticalCylinderMap_regular hs _)
    · exact cyclic_coordinate_same_fibers e ht A ainj st _ per
  · have lognz : Real.log a≠0 := fun eq => one ((Real.exp_log ha).symm.trans (by rw [eq,Real.exp_zero]))
    obtain ⟨s,hs,sig⟩ := abs_period_scale lognz
    let q := b/(1-a)
    let A := fun z : RiemannUnitDisk => boundaryLogCoordinate u q z.1
    have ainj : Function.Injective A := fun x y h => Subtype.ext (boundaryLogCoordinate_injOn hu q x.2 y.2 h)
    have st (z : ℂ) : A (e (z+t))=A (e z)+(Real.log a:ℂ) := by
      rw [step]
      exact disk_boundary_log_step ha one hu (disk_point_norm _) (action _)
    have per (v w : ℂ) : horizontalCylinderMap s v=horizontalCylinderMap s w ↔ ∃ n : ℤ, v=w+(n:ℂ)*(Real.log a:ℂ) :=
      (horizontalCylinderMap_fibers hs v w).trans (integer_shifts_same_up_to_sign sig v w)
    let c := Real.pi/2
    have hc : 0<c := half_pos Real.pi_pos
    let R := Real.exp (c/s)
    have hr : 1<R := Real.one_lt_exp_iff.mpr (div_pos hc hs)
    refine ⟨horizontalCylinderMap s ∘ boundaryLogCoordinate u q,_,Or.inr (Or.inr ⟨R,hr,rfl⟩),?_,?_,?_⟩
    · rw [image_comp,boundaryLogCoordinate_range hu]
      simpa only [R,c,neg_div,Real.exp_neg] using horizontalCylinderMap_range hs hc
    · intro z hz
      exact analytic_regular_comp (boundaryLogCoordinate_regular hu q (by simpa using (show z∈ball 0 1 from hz))) (horizontalCylinderMap_regular hs _)
    · exact cyclic_coordinate_same_fibers e ht A ainj st _ per

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disk_cyclic_quotient_parameter
