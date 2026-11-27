import TwoAxisHelicoid.SmoothAnnularRadius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace TwoAxisHelicoid
open Set Real
open scoped Topology ContDiff

noncomputable def annularRadialMap (f : ℝ → ℝ) (z : ℂ) : ℂ := (f ‖z‖/‖z‖) • z

theorem annularRadialMap_norm {f : ℝ → ℝ} {z : ℂ} (nz : 0<‖z‖) (hz : 0≤f ‖z‖) :
    ‖annularRadialMap f z‖=f ‖z‖ := by
  rw [annularRadialMap,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hz nz.le),div_mul_cancel₀ _ nz.ne']

theorem annularRadialMap_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {z : ℂ} (nz : z≠0) :
    ContDiffAt ℝ ∞ (annularRadialMap f) z := by
  have hn : ContDiffAt ℝ ∞ (norm : ℂ → ℝ) z := contDiffAt_norm ℝ nz
  exact ((hf.contDiffAt.comp z hn).div hn (norm_ne_zero_iff.mpr nz)).smul contDiffAt_id

private theorem radial_inverse {f g : ℝ → ℝ} {z : ℂ} (nz : 0<‖z‖) (fz : 0<f ‖z‖)
    (back : g (f ‖z‖)=‖z‖) : annularRadialMap g (annularRadialMap f z)=z := by
  change (g ‖annularRadialMap f z‖/‖annularRadialMap f z‖) • annularRadialMap f z=z
  rw [annularRadialMap_norm nz fz.le,back,annularRadialMap,smul_smul]
  rw [show ‖z‖/f ‖z‖*(f ‖z‖/‖z‖)=1 by field_simp,one_smul]

/-- A finite round annulus admits a smooth punctured-disk coordinate
agreeing with its original holomorphic coordinate throughout the outer
collar. The two directions have explicit radial norm formulae. -/
theorem smooth_round_annulus_puncture {r s R : ℝ} (hr : 0≤r) (rs : r<s) (sr : s<R) :
    ∃ (e : ℝ ≃o ℝ) (d : OpenPartialHomeomorph ℂ ℂ), e r=0 ∧
      d.source={z : ℂ | r<‖z‖ ∧ ‖z‖<R} ∧ d.target={z : ℂ | 0<‖z‖ ∧ ‖z‖<R} ∧
      (∀ z∈d.source, ‖d z‖=e ‖z‖ ∧ ContDiffAt ℝ ∞ d z) ∧
      (∀ z∈d.target, ‖d.symm z‖=e.symm ‖z‖ ∧ ContDiffAt ℝ ∞ d.symm z) ∧
      (∀ z : ℂ, s≤‖z‖ → d z=z) ∧ (∀ z : ℂ, s≤‖z‖ → d.symm z=z) := by
  obtain ⟨e,er,fixed,hs,hi⟩ := smooth_annular_radius hr rs
  have isfixed (x : ℝ) (hx : s≤x) : e.symm x=x := e.symm_apply_eq.mpr (fixed x hx).symm
  have eR := fixed R sr.le
  have ei0 : e.symm 0=r := e.symm_apply_eq.mpr er.symm
  have eiR := isfixed R sr.le
  have fpos {z : ℂ} (h : r<‖z‖) : 0<e ‖z‖ := er ▸ e.strictMono h
  have ipos {z : ℂ} (h : 0<‖z‖) : r<e.symm ‖z‖ := ei0 ▸ e.symm.strictMono h
  let d : OpenPartialHomeomorph ℂ ℂ := {
    toFun := annularRadialMap e
    invFun := annularRadialMap e.symm
    source := {z | r<‖z‖ ∧ ‖z‖<R}
    target := {z | 0<‖z‖ ∧ ‖z‖<R}
    map_source' := fun z h => by
      change 0<‖annularRadialMap e z‖ ∧ ‖annularRadialMap e z‖<R
      rw [annularRadialMap_norm (hr.trans_lt h.1) (fpos h.1).le]
      exact ⟨fpos h.1,eR ▸ e.strictMono h.2⟩
    map_target' := fun z h => by
      change r<‖annularRadialMap e.symm z‖ ∧ ‖annularRadialMap e.symm z‖<R
      rw [annularRadialMap_norm h.1 (hr.trans (ipos h.1).le)]
      exact ⟨ipos h.1,eiR ▸ e.symm.strictMono h.2⟩
    left_inv' := fun z h => radial_inverse (hr.trans_lt h.1) (fpos h.1) (e.symm_apply_apply _)
    right_inv' := fun z h => radial_inverse h.1 (hr.trans_lt (ipos h.1)) (e.apply_symm_apply _)
    open_source := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    open_target := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    continuousOn_toFun := fun z h => (annularRadialMap_smooth hs (norm_pos_iff.mp (hr.trans_lt h.1))).continuousAt.continuousWithinAt
    continuousOn_invFun := fun z h => (annularRadialMap_smooth hi (norm_pos_iff.mp h.1)).continuousAt.continuousWithinAt }
  refine ⟨e,d,er,rfl,rfl,fun z h => ⟨annularRadialMap_norm (hr.trans_lt h.1) (fpos h.1).le,
    annularRadialMap_smooth hs (norm_pos_iff.mp (hr.trans_lt h.1))⟩,fun z h => ⟨annularRadialMap_norm h.1
    (hr.trans (ipos h.1).le),annularRadialMap_smooth hi (norm_pos_iff.mp h.1)⟩,?_,?_⟩
  · intro z hz
    change (e ‖z‖/‖z‖) • z=z
    rw [fixed _ hz,div_self (hr.trans_lt (rs.trans_le hz)).ne',one_smul]
  · intro z hz
    change (e.symm ‖z‖/‖z‖) • z=z
    rw [isfixed _ hz,div_self (hr.trans_lt (rs.trans_le hz)).ne',one_smul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_round_annulus_puncture

