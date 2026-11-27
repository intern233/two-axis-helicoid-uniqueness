import TwoAxisHelicoid.PlaneRadialDevelopment
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Schwarz

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function
open scoped Topology ContDiff

/-- A C² planar map with a lower bound on every real differential
has an inverse branch on the indicated target disk, centered at the
chosen point. Only the lower bound and the available physical radius
enter the size of that disk. -/
theorem quantitative_plane_inverse_disk {F : ℂ → ℂ} {a : ℂ} {R M r : ℝ}
    (Rp : 0<R) (mp : 0≤M) (rp : 0<r) (room : M*r<R/2)
    (smooth : ContDiffOn ℝ 2 F (ball a R))
    (lower : ∀ z∈ball a R, ∀ v, ‖v‖≤M*‖fderiv ℝ F z v‖) :
    ∃ s : ℂ → ℂ, s (F a)=a ∧ ∀ w∈ball (F a) r, s w∈ball a (R/2) ∧ F (s w)=w ∧
      HasFDerivAt s (ContinuousLinearMap.inverse (fderiv ℝ F (s w))) w := by
  let χ : ContDiffBump a := ⟨R/2,3*R/4,by linarith,by linarith⟩
  let D := fderiv ℝ F
  have equivalence (z : ℂ) (hz : z∈ball a R) : ∃ e : ℂ ≃L[ℝ] ℂ, (e : ℂ →L[ℝ] ℂ)=D z := by
    have inj : Injective (D z) := by
      intro v w eq
      apply sub_eq_zero.mp
      have b := lower z hz (v-w)
      change ‖v-w‖≤M*‖D z (v-w)‖ at b
      rw [map_sub,eq,sub_self,norm_zero,mul_zero] at b
      exact norm_le_zero_iff.mp b
    let e := (LinearEquiv.ofBijective (D z).toLinearMap ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩).toContinuousLinearEquiv
    exact ⟨e,rfl⟩
  let A := fun z => χ z • ContinuousLinearMap.inverse (D z)
  have outside {z : ℂ} (hz : z∉ball a R) : A =ᶠ[𝓝 z] 0 := by
    have far : 3*R/4<dist z a := (show 3*R/4<R by linarith).trans_le (le_of_not_gt hz)
    filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds far] with w hw
    change χ w • ContinuousLinearMap.inverse (D w)=0
    change 3*R/4<dist w a at hw
    rw [χ.zero_of_le_dist hw.le,zero_smul]
  have sa : ContDiff ℝ 1 A := contDiff_iff_contDiffAt.mpr fun z => by
    by_cases hz : z∈ball a R
    · obtain ⟨e,eq⟩ := equivalence z hz
      have ds : ContDiffAt ℝ 1 D z := ((smooth z hz).contDiffAt (isOpen_ball.mem_nhds hz)).fderiv_right (by norm_num)
      have inv : ContDiffAt ℝ 1 ContinuousLinearMap.inverse (D z) := eq ▸ contDiffAt_map_inverse e
      exact χ.contDiff.contDiffAt.smul (inv.comp z ds)
    · exact contDiffAt_const.congr_of_eventuallyEq (outside hz)
  have ba (z : ℂ) : ‖A z‖≤M := by
    by_cases hz : z∈ball a R
    · obtain ⟨e,eq⟩ := equivalence z hz
      have op : ‖(e.symm : ℂ →L[ℝ] ℂ)‖≤M := ContinuousLinearMap.opNorm_le_bound _ mp fun v => by
        have h := lower z hz (e.symm v)
        change ‖e.symm v‖≤M*‖D z (e.symm v)‖ at h
        simpa only [← eq,ContinuousLinearEquiv.coe_coe,e.apply_symm_apply] using h
      change ‖χ z • ContinuousLinearMap.inverse (D z)‖≤M
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg χ.nonneg,← eq,ContinuousLinearMap.inverse_equiv]
      exact (mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg _)).trans (by simpa only [one_mul] using op)
    · rw [(outside hz).self_of_nhds]
      simpa only [Pi.zero_apply,norm_zero] using mp
  have agrees {z : ℂ} (hz : z∈ball a (R/2)) : A z=ContinuousLinearMap.inverse (D z) := by
    change χ z • ContinuousLinearMap.inverse (D z)=_
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hz),one_smul]
  have df (z : ℂ) (hz : z∈ball a (R/2)) : ∃ e : ℂ ≃L[ℝ] ℂ, HasFDerivAt F (e : ℂ →L[ℝ] ℂ) z ∧
      (e.symm : ℂ →L[ℝ] ℂ)=A z := by
    have hb : z∈ball a R := ball_subset_ball (by linarith : R/2≤R) hz
    obtain ⟨e,eq⟩ := equivalence z hb
    refine ⟨e,eq.symm ▸ (((smooth z hb).contDiffAt (isOpen_ball.mem_nhds hb)).differentiableAt (by norm_num)).hasFDerivAt,?_⟩
    rw [agrees hz,← eq,ContinuousLinearMap.inverse_equiv]
  obtain ⟨s,center,branch⟩ := radial_inverse_branch_on_disk mp rp room sa ba df
  refine ⟨s,center,?_⟩
  intro w hw
  obtain ⟨inside,right,ds⟩ := branch w hw
  exact ⟨inside,right,(agrees inside) ▸ ds⟩

/-- A bounded Gauss coordinate expressed in physical planar parameters
obeys a Cauchy estimate as soon as it is holomorphic relative to the
developing coordinate. The derivative bound uses the realized target disk. -/
theorem quantitative_developed_cauchy_estimate {F G q : ℂ → ℂ} {a : ℂ} {R M r B : ℝ}
    (Rp : 0<R) (mp : 0≤M) (rp : 0<r) (room : M*r<R/2)
    (smooth : ContDiffOn ℝ 2 F (ball a R))
    (lower : ∀ z∈ball a R, ∀ v, ‖v‖≤M*‖fderiv ℝ F z v‖)
    (coefficient : ∀ z∈ball a R, HasFDerivAt G
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (q z)).restrictScalars ℝ).comp (fderiv ℝ F z)) z)
    (bounded : ∀ z∈ball a R, ‖G z‖≤B) : ‖q a‖≤2*B/r := by
  obtain ⟨s,start,branch⟩ := quantitative_plane_inverse_disk Rp mp rp room smooth lower
  have inside {w : ℂ} (hw : w∈ball (F a) r) : s w∈ball a R :=
    ball_subset_ball (by linarith : R/2≤R) (branch w hw).1
  have derivative {w : ℂ} (hw : w∈ball (F a) r) : HasDerivAt (G ∘ s) (q (s w)) w := by
    obtain ⟨_,_,ds⟩ := branch w hw
    have df := ((smooth _ (inside hw)).contDiffAt (isOpen_ball.mem_nhds (inside hw))).differentiableAt (by norm_num)
    have localId : (id : ℂ → ℂ) =ᶠ[𝓝 w] F ∘ s := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      exact (branch v hv).2.1.symm
    have id := (df.hasFDerivAt.comp w ds).congr_of_eventuallyEq localId
    have one := id.unique (hasFDerivAt_id w)
    have h := (coefficient _ (inside hw)).comp w ds
    let c := (1 : ℂ →L[ℂ] ℂ).smulRight (q (s w))
    have hc : HasFDerivAt (G ∘ s) c w := by
      apply hasFDerivAt_of_restrictScalars ℝ h
      ext v
      have eq := DFunLike.congr_fun one v
      change fderiv ℝ F (s w) ((ContinuousLinearMap.inverse (fderiv ℝ F (s w))) v)=v at eq
      change v*q (s w)=(fderiv ℝ F (s w) ((ContinuousLinearMap.inverse (fderiv ℝ F (s w))) v))*q (s w)
      rw [eq]
    have val : c 1=q (s w) := by change 1*q (s w)=_;rw [one_mul]
    exact val ▸ hc.hasDerivAt
  have center := Metric.mem_ball_self rp (x:=F a)
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball (fun w hw => (derivative hw).differentiableAt.differentiableWithinAt)
    (f:=G ∘ s) (R₂:=2*B) (by
      intro w hw
      change dist (G (s w)) (G (s (F a)))≤2*B
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [bounded _ (inside hw),bounded _ (inside center)])) rp
  simpa only [(derivative center).deriv,start] using h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quantitative_plane_inverse_disk
#print axioms TwoAxisHelicoid.quantitative_developed_cauchy_estimate
