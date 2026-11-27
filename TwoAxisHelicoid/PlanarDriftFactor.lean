import TwoAxisHelicoid.PlanarBoundaryDriftContact

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace Laplacian
open scoped Topology

/-- A scalar surface equation represented by a nonvanishing analytic
factor times a solution of a planar linear drift equation. -/
def HasPlanarDriftFactorAt (F : ℂ → ℝ) (z : ℂ) : Prop :=
  ∃ C f A B : ℂ → ℝ, AnalyticAt ℝ C z ∧ C z ≠ 0 ∧ AnalyticAt ℝ f z ∧ ContinuousAt A z ∧ ContinuousAt B z ∧
    (F =ᶠ[𝓝 z] fun w => C w*f w) ∧ ∀ᶠ w in 𝓝 z, (Δ f) w=A w*planePartial 1 f w+B w*planePartial I f w

private theorem ordered_factor {F C f : ℂ → ℝ} {z : ℂ} {S : Set ℂ}
    (cc : ContinuousAt C z) (nc : C z ≠ 0) (eq : F =ᶠ[𝓝 z] fun w => C w*f w)
    (side : (∀ᶠ w in 𝓝 z, w ∈ S → 0≤F w) ∨ (∀ᶠ w in 𝓝 z, w ∈ S → F w≤0)) :
    (∀ᶠ w in 𝓝 z, w ∈ S → 0≤f w) ∨ (∀ᶠ w in 𝓝 z, w ∈ S → f w≤0) := by
  rcases lt_or_gt_of_ne nc with neg | pos
  · have near := cc.eventually_lt continuousAt_const neg
    rcases side with nn | np
    · right
      filter_upwards [near,eq,nn] with w cw e hw hS
      have h := e ▸ hw hS
      exact le_of_not_gt fun hp => (mul_neg_of_neg_of_pos cw hp).not_ge h
    · left
      filter_upwards [near,eq,np] with w cw e hw hS
      have h := e ▸ hw hS
      exact le_of_not_gt fun hp => (mul_pos_of_neg_of_neg cw hp).not_ge h
  · have near := continuousAt_const.eventually_lt cc pos
    rcases side with nn | np
    · left
      filter_upwards [near,eq,nn] with w cw e hw hS
      have h := e ▸ hw hS
      exact le_of_not_gt fun hp => (mul_neg_of_pos_of_neg cw hp).not_ge h
    · right
      filter_upwards [near,eq,np] with w cw e hw hS
      have h := e ▸ hw hS
      exact le_of_not_gt fun hp => (mul_pos cw hp).not_ge h

theorem HasPlanarDriftFactorAt.interior_contact {F : ℂ → ℝ} {z : ℂ} (h : HasPlanarDriftFactorAt F z)
    (zero : F z=0) (side : (∀ᶠ w in 𝓝 z, 0≤F w) ∨ (∀ᶠ w in 𝓝 z, F w≤0)) : F =ᶠ[𝓝 z] 0 := by
  obtain ⟨C,f,A,B,cc,nc,af,ca,cb,eq,sol⟩ := h
  have atz : f z=0 := (mul_eq_zero.mp (eq.self_of_nhds.symm.trans zero)).resolve_left nc
  have ord := ordered_factor (S := univ) cc.continuousAt nc eq (by simpa using side)
  have done := planar_drift_one_sided_contact af ca cb atz (by simpa using ord) sol
  filter_upwards [eq,done] with w e he
  change F w=0
  change f w=0 at he
  rw [e,he,mul_zero]

theorem HasPlanarDriftFactorAt.boundary_contact {F : ℂ → ℝ} {z : ℂ} {S : Set ℂ}
    (h : HasPlanarDriftFactorAt F z) (disks : HasInwardTangentDisksAt S z)
    (zero : F z=0) (flat : fderiv ℝ F z=0)
    (side : (∀ᶠ w in 𝓝 z, w ∈ S → 0≤F w) ∨ (∀ᶠ w in 𝓝 z, w ∈ S → F w≤0)) :
    F =ᶠ[𝓝 z] 0 := by
  obtain ⟨C,f,A,B,ac,nc,af,ca,cb,eq,sol⟩ := h
  have atz : f z=0 := (mul_eq_zero.mp (eq.self_of_nhds.symm.trans zero)).resolve_left nc
  have dz := (ac.differentiableAt.hasFDerivAt.mul af.differentiableAt.hasFDerivAt).congr_of_eventuallyEq eq
  have grad : fderiv ℝ f z=0 := by
    have e := dz.fderiv.symm.trans flat
    rw [atz,zero_smul,add_zero] at e
    exact (smul_eq_zero.mp e).resolve_left nc
  have done := planar_drift_boundary_tangent_contact disks af ca cb sol atz grad (ordered_factor ac.continuousAt nc eq side)
  filter_upwards [eq,done] with w e he
  change F w=0
  change f w=0 at he
  rw [e,he,mul_zero]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasPlanarDriftFactorAt.interior_contact
#print axioms TwoAxisHelicoid.HasPlanarDriftFactorAt.boundary_contact
