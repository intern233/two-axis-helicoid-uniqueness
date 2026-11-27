import TwoAxisHelicoid.AnalyticRadialLeadingProfile
import TwoAxisHelicoid.AnalyticPlaneLaplacian
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

namespace TwoAxisHelicoid
open Complex Filter Topology Set Function InnerProductSpace Laplacian
open scoped ContDiff Topology

private theorem smooth_plane_partial {f : ℂ → ℝ} (sm : ContDiff ℝ ∞ f) (v : ℂ) :
    ContDiff ℝ ∞ (planePartial v f) :=
  (contDiff_infty_iff_fderiv.mp sm).2.clm_apply contDiff_const

private theorem smooth_plane_laplace_trace {f : ℂ → ℝ} (sm : ContDiff ℝ ∞ f) (z : ℂ) :
    (Δ f) z=planePartial 1 (planePartial 1 f) z+planePartial I (planePartial I f) z := by
  have d (v : ℂ) : planePartial v (planePartial v f) z=fderiv ℝ (fderiv ℝ f) z v v := by
    have deriv := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z
      (((contDiff_infty_iff_fderiv.mp sm).2.differentiable (by norm_num) z).hasFDerivAt)
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ f) z v=_
    rw [deriv.fderiv]
    rfl
  simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,d,
    Matrix.cons_val_zero,Matrix.cons_val_one]

private theorem dilation_partial {f : ℂ → ℝ} (sm : ContDiff ℝ ∞ f) (x v w : ℂ) (r : ℝ) :
    planePartial v (fun z => f (x+r • z)) w=r*planePartial v f (x+r • w) := by
  have scale : HasFDerivAt (fun z : ℂ => x+r • z) (r • ContinuousLinearMap.id ℝ ℂ) w :=
    ((hasFDerivAt_id w).const_smul r).const_add x
  have d := ((sm.differentiable (by norm_num) _).hasFDerivAt).comp w scale
  change (fderiv ℝ (fun z : ℂ => f (x+r • z)) w) v=_
  rw [show fderiv ℝ (fun z : ℂ => f (x+r • z)) w=_ from d.fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul,planePartial]

private theorem scaled_partial {f : ℂ → ℝ} (sm : ContDiff ℝ ∞ f) (v w : ℂ) (s : ℝ) :
    planePartial v (fun z => s*f z) w=s*planePartial v f w :=
  congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (((sm.differentiable (by norm_num) w).hasFDerivAt).const_smul s).fderiv

private theorem dilation_laplacian {f : ℂ → ℝ} (sm : ContDiff ℝ ∞ f) (x w : ℂ) (r : ℝ) :
    (Δ (fun z : ℂ => f (x+r • z))) w=r^2*(Δ f) (x+r • w) := by
  have smoothV : ContDiff ℝ ∞ (fun z : ℂ => x+r • z) := contDiff_const.add ((r • ContinuousLinearMap.id ℝ ℂ).contDiff)
  have second (v : ℂ) :
      planePartial v (planePartial v (fun z : ℂ => f (x+r • z))) w=
        r^2*planePartial v (planePartial v f) (x+r • w) := by
    have sc : ContDiff ℝ ∞ (fun z : ℂ => planePartial v f (x+r • z)) := (smooth_plane_partial sm v).comp smoothV
    rw [funext (fun z => dilation_partial sm x v z r),scaled_partial sc v w r,
      dilation_partial (smooth_plane_partial sm v) x v w r]
    ring
  have sc : ContDiff ℝ ∞ (fun z : ℂ => f (x+r • z)) := sm.comp smoothV
  rw [smooth_plane_laplace_trace sc,smooth_plane_laplace_trace sm,second,second]
  ring

private noncomputable def slicePartial (H : ℝ × ℂ → ℝ) (u : ℂ) (p : ℝ × ℂ) : ℝ :=
  fderiv ℝ H p (0,u)

private theorem smooth_slice_partial {H : ℝ × ℂ → ℝ} (sm : ContDiff ℝ ∞ H) (u : ℂ) :
    ContDiff ℝ ∞ (slicePartial H u) := (contDiff_infty_iff_fderiv.mp sm).2.clm_apply contDiff_const

private theorem slice_partial_apply {H : ℝ × ℂ → ℝ} (sm : ContDiff ℝ ∞ H) (r : ℝ) (u v : ℂ) :
    planePartial u (fun w : ℂ => H (r,w)) v=slicePartial H u (r,v) := by
  have d := ((sm.differentiable (by norm_num) (r,v)).hasFDerivAt).comp v (hasFDerivAt_prodMk_right r v)
  exact congrArg (fun T : ℂ →L[ℝ] ℝ => T u) d.fderiv

/-- The first smooth radial profile of a planar solution of the drift
equation is harmonic on the entire tangent plane and homogeneous of
its vanishing degree. Continuity of the two drift coefficients at the
contact point suffices. -/
theorem radial_profile_harmonic_homogeneous {f A B : ℂ → ℝ} {x : ℂ} (sm : ContDiff ℝ ∞ f)
    (ca : ContinuousAt A x) (cb : ContinuousAt B x)
    (pde : ∀ᶠ z in 𝓝 x, (Δ f) z=A z*planePartial 1 f z+B z*planePartial I f z)
    {n : ℕ} {H : ℝ × ℂ → ℝ} (sh : ContDiff ℝ ∞ H) (form : ∀ r v, f (x+r • v)=r^n*H (r,v)) :
    (∀ v, HarmonicAt (fun w : ℂ => H (0,w)) v) ∧ ∀ c : ℝ, ∀ v, H (0,c • v)=c^n*H (0,v) := by
  let V := fun r : ℝ => fun v : ℂ => H (r,v)
  have sv (r : ℝ) : ContDiff ℝ ∞ (V r) := sh.comp (contDiff_const.prodMk contDiff_id)
  have firstOrder (r : ℝ) (v d : ℂ) : r*planePartial d f (x+r • v)=r^n*planePartial d (V r) v := by
    exact (dilation_partial sm x d v r).symm.trans ((congrArg (fun g : ℂ → ℝ => planePartial d g v)
      (funext (form r))).trans (scaled_partial (sv r) d v (r^n)))
  have lap (r : ℝ) (v : ℂ) : r^n*(Δ (V r)) v=r^2*(Δ f) (x+r • v) := by
    have eq := congrArg (fun g : ℂ → ℝ => (Δ g) v) (funext (form r))
    exact (show (Δ (r^n • V r)) v=r^n*(Δ (V r)) v from laplacian_smul _ ((sv r).contDiffAt.of_le (by norm_num))).symm.trans
      (eq.symm.trans (dilation_laplacian sm x v r))
  have slice2 (r : ℝ) (v d : ℂ) : planePartial d (planePartial d (V r)) v=slicePartial (slicePartial H d) d (r,v) := by
    rw [show planePartial d (V r)=(fun w => slicePartial H d (r,w)) from funext (slice_partial_apply sh r d)]
    exact slice_partial_apply (smooth_slice_partial sh d) r d v
  have lapZero (v : ℂ) : (Δ (V 0)) v=0 := by
    have lin : Tendsto (fun r : ℝ => x+r • v) (𝓝 0) (𝓝 x) := by
      have a : Continuous (fun r : ℝ => x+r • v) := continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul,add_zero] using (a.continuousAt (x:=(0:ℝ))).tendsto
    have eq : (fun r : ℝ => (Δ (V r)) v) =ᶠ[𝓝[≠] 0] fun r =>
        r*(A (x+r • v)*slicePartial H 1 (r,v)+B (x+r • v)*slicePartial H I (r,v)) := by
      filter_upwards [lin.eventually pde |>.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r e nz
      apply mul_left_cancel₀ (pow_ne_zero n (show r≠0 from nz))
      calc
        r^n*(Δ (V r)) v=r^2*(Δ f) (x+r • v) := lap r v
        _=r*(A (x+r • v)*(r*planePartial 1 f (x+r • v))+B (x+r • v)*(r*planePartial I f (x+r • v))) := by rw [e]; ring
        _=_ := by rw [firstOrder,firstOrder,slice_partial_apply sh r 1 v,slice_partial_apply sh r I v]; ring
    have pin : Continuous (fun r : ℝ => (r,v)) := continuous_id.prodMk continuous_const
    have cl : Continuous (fun r : ℝ => (Δ (V r)) v) := by
      simp_rw [smooth_plane_laplace_trace (sv _),slice2]
      exact (((smooth_slice_partial (smooth_slice_partial sh 1) 1).continuous.comp pin).add
        ((smooth_slice_partial (smooth_slice_partial sh I) I).continuous.comp pin))
    have cr := (show Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0) from tendsto_id).mul (((ca.tendsto.comp lin).mul
      (((smooth_slice_partial sh 1).continuous.comp pin).continuousAt)).add ((cb.tendsto.comp lin).mul
      (((smooth_slice_partial sh I).continuous.comp pin).continuousAt)))
    exact (tendsto_nhds_unique_of_eventuallyEq cl.continuousAt.continuousWithinAt (cr.mono_left nhdsWithin_le_nhds) eq).trans (zero_mul _)
  refine ⟨fun v => ⟨(sv 0).contDiffAt.of_le (by norm_num),Eventually.of_forall lapZero⟩,?_⟩
  intro c v
  have eq : (fun r : ℝ => H (r,c • v)) =ᶠ[𝓝[≠] 0] fun r => c^n*H (r*c,v) := by
    filter_upwards [self_mem_nhdsWithin] with r nz
    apply mul_left_cancel₀ (pow_ne_zero n (show r≠0 from nz))
    calc r^n*H (r,c • v)=f (x+(r*c) • v) := by rw [← form,smul_smul]
         _=(r*c)^n*H (r*c,v) := form _ _
         _=_ := by rw [mul_pow,mul_assoc]
  have l : Continuous (fun r : ℝ => H (r,c • v)) := sh.continuous.comp (continuous_id.prodMk continuous_const)
  have right : Continuous (fun r : ℝ => c^n*H (r*c,v)) := continuous_const.mul
    (sh.continuous.comp ((continuous_id.mul continuous_const).prodMk continuous_const))
  simpa only [zero_mul] using tendsto_nhds_unique_of_eventuallyEq l.continuousAt.continuousWithinAt right.continuousAt.continuousWithinAt eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.radial_profile_harmonic_homogeneous
