import TwoAxisHelicoid.RoundLogarithmicCover
import TwoAxisHelicoid.HalfPlaneDeckCoordinates

namespace TwoAxisHelicoid
open Complex Filter Set Metric Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

private theorem disk_biholomorphic_image (T : Opens ℂ) (F : ℂ → ℂ)
    (reg : ∀ z∈complexUnitDisk, AnalyticAt ℂ F z ∧ deriv F z≠0)
    (image : F '' complexUnitDisk=(T : Set ℂ)) (inj : InjOn F complexUnitDisk) :
    Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) RiemannUnitDisk T ω) := by
  let U := Diffeomorph.refl 𝓘(ℂ,ℂ) RiemannUnitDisk ω
  obtain ⟨G,_⟩ := analytic_function_uniformizes_quotient unitDiskOpen T U.isLocalDiffeomorph U.surjective F reg image
    (fun a b => ⟨fun eq => congrArg U (Subtype.ext (inj a.2 b.2 eq)),fun eq => congrArg (fun z : RiemannUnitDisk => F z.1) (U.injective eq)⟩)
  exact ⟨G⟩

private theorem regular_complex_scale (c : ℂ) (nc : c≠0) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => c*w) z ∧ deriv (fun w : ℂ => c*w) z≠0 := by
  refine ⟨analyticAt_const.mul analyticAt_id,?_⟩
  simpa using nc

/-- The logarithmic preimage of every round cylinder is either the
plane or the disk as a complex manifold. For the finite annulus the
coordinate is an explicit scaled, rotated logarithmic Cayley map. -/
theorem round_log_domain_plane_or_disk (T : Opens ℂ) (shape : IsRoundCylinderTarget T) :
    Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ℂ (roundLogDomain T) ω) ∨
    Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) RiemannUnitDisk (roundLogDomain T) ω) := by
  have small {z : ℂ} (h : z∈complexUnitDisk) : ‖z‖<1 := by simpa only [complexUnitDisk,mem_ball,dist_zero_right] using h
  have hu : ‖(1:ℂ)‖=1 := norm_one
  rcases shape with whole|punct|⟨R,hR,ann⟩
  · left
    have all : roundLogDomain T=⊤ := by
      ext w
      change Complex.exp w∈(T:Set ℂ) ↔ True
      rw [whole]
      exact iff_true_intro (norm_pos_iff.mpr (Complex.exp_ne_zero _))
    rw [all]
    refine ⟨{
      toFun := fun z => ⟨z,mem_univ _⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_invFun := contMDiff_subtype_val
      contMDiff_toFun := ?_ }⟩
    intro z
    rw [← contMDiffWithinAt_univ]
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).mp contMDiffWithinAt_id
  · right
    let F := fun z : ℂ => -boundaryCayley 1 z
    have img : F '' complexUnitDisk=(roundLogDomain T:Set ℂ) := by
      change (Neg.neg ∘ boundaryCayley 1) '' complexUnitDisk=_
      rw [image_comp,boundaryCayley_exact_range hu]
      ext w
      change (∃ x : ℂ, 0<x.re ∧ -x=w) ↔ Complex.exp w∈(T:Set ℂ)
      rw [punct]
      change _ ↔ 0<‖Complex.exp w‖ ∧ ‖Complex.exp w‖<1
      rw [Complex.norm_exp,Real.exp_lt_one_iff]
      constructor
      · rintro ⟨x,h,rfl⟩
        exact ⟨Real.exp_pos _,by simpa using h⟩
      · intro h
        exact ⟨-w,by simpa using h.2,neg_neg w⟩
    refine disk_biholomorphic_image _ F ?_ img ?_
    · intro z hz
      have r := boundaryCayley_regular hu (small hz)
      exact ⟨r.1.neg,by simpa only [F,deriv.fun_neg,neg_ne_zero] using r.2⟩
    · intro x hx y hy h
      have same := neg_injective h
      exact (boundaryCayley_left_inv hu (small hx)).symm.trans ((congrArg (boundaryCayleyInv 1) same).trans
        (boundaryCayley_left_inv hu (small hy)))
  · right
    let b := Real.pi/2
    let k := Real.log R/b
    have bp : 0<b := half_pos Real.pi_pos
    have lp := Real.log_pos hR
    have kp : 0<k := div_pos lp bp
    have kb : k*b=Real.log R := div_mul_cancel₀ _ bp.ne'
    let c : ℂ := (k:ℂ)*I
    have cn : c≠0 := mul_ne_zero (ofReal_ne_zero.mpr kp.ne') I_ne_zero
    let A := boundaryLogCoordinate 1 0
    let F := (fun z : ℂ => c*z) ∘ A
    have test (v : ℂ) : c*v∈roundLogDomain T ↔ |v.im|<b := by
      change Complex.exp (c*v)∈(T:Set ℂ) ↔ _
      rw [ann]
      change R⁻¹<‖Complex.exp (c*v)‖ ∧ ‖Complex.exp (c*v)‖<R ↔ _
      have pos := zero_lt_one.trans hR
      have inv : R⁻¹=Real.exp (-Real.log R) := by rw [Real.exp_neg,Real.exp_log pos]
      rw [Complex.norm_exp,inv,Real.exp_lt_exp,← Real.lt_log_iff_exp_lt pos,← abs_lt]
      have re : (c*v).re= -(k*v.im) := by simp [c,Complex.mul_re,Complex.mul_im]
      rw [re,abs_neg,abs_mul,abs_of_pos kp,← kb]
      exact mul_lt_mul_iff_right₀ kp
    have img : F '' complexUnitDisk=(roundLogDomain T:Set ℂ) := by
      rw [show F=(fun z : ℂ => c*z) ∘ boundaryLogCoordinate 1 0 from rfl,image_comp,boundaryLogCoordinate_range hu]
      ext w
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact (test v).mpr hv
      · intro hw
        obtain ⟨v,hv⟩ := (Homeomorph.mulLeft₀ c cn).surjective w
        change c*v=w at hv
        exact ⟨v,(test v).mp (hv.symm ▸ hw),hv⟩
    refine disk_biholomorphic_image _ F ?_ img ?_
    · intro z hz
      exact analytic_regular_comp (boundaryLogCoordinate_regular hu 0 (small hz)) (regular_complex_scale c cn _)
    · intro x hx y hy h
      exact boundaryLogCoordinate_injOn hu 0 hx hy (mul_left_cancel₀ cn h)

/-- Standard simply connected holomorphic covers for all three round
targets, with the actual covering and local diffeomorphism properties. -/
theorem round_cylinder_holomorphic_universal_cover (T : Opens ℂ) (shape : IsRoundCylinderTarget T) :
    (∃ p : ℂ → T, IsCoveringMap p ∧ Surjective p ∧ IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p) ∨
    (∃ p : RiemannUnitDisk → T, IsCoveringMap p ∧ Surjective p ∧ IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p) := by
  have nz (z : ℂ) (hz : z∈T) : z≠0 := by
    change z∈(T : Set ℂ) at hz
    rcases shape with whole|punct|⟨R,rp,ann⟩
    · rw [whole] at hz
      exact norm_pos_iff.mp hz
    · rw [punct] at hz
      exact norm_pos_iff.mp hz.1
    · rw [ann] at hz
      have l := hz.1
      exact norm_pos_iff.mp ((inv_pos.mpr (zero_lt_one.trans rp)).trans l)
  obtain ⟨p,cover,onto,hol⟩ := round_log_domain_exponential T nz
  rcases round_log_domain_plane_or_disk T shape with left|right
  · obtain ⟨E⟩ := left
    exact Or.inl ⟨p ∘ E,cover.comp_homeomorph E.toHomeomorph,onto.comp E.surjective,
      fun z => IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := T) (E.isLocalDiffeomorph z) (hol _)⟩
  · obtain ⟨E⟩ := right
    exact Or.inr ⟨p ∘ E,cover.comp_homeomorph E.toHomeomorph,onto.comp E.surjective,
      fun z => IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := T) (E.isLocalDiffeomorph z) (hol _)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.round_log_domain_plane_or_disk
#print axioms TwoAxisHelicoid.round_cylinder_holomorphic_universal_cover
