import TwoAxisHelicoid.TraceDataSlopingFluxGroup23
import TwoAxisHelicoid.SlopingFluxRootParameters
import TwoAxisHelicoid.UnivalentQuarterHeightCoordinate
import TwoAxisHelicoid.CentralHeightArcDerivative
import TwoAxisHelicoid.CoordinateDataSymmetry

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaA

private theorem last_sloping_upper_bound :
    let B := TraceData.slopingFluxCell188.plusTheta.output.toBall TraceData.slopingFluxDataSetup.config.prec
    B.center.im+B.radius< -3 := by decide +kernel

/-- The actual real and imaginary coordinate differentials at the
central half period, with the sign resolved by the last cell of the
original generator certificate. In conjugate height the unit tangent
of the horizontal section points in the negative first direction. -/
theorem central_half_period_tangent_orientation {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) (ab : a∈Ioo (0:ℝ) 1) :
    let p : ℂ := (1+I*t)/2
    let D := coordinateData t a 1 hp p
    3<(D 2).re ∧ D 0=I*D 2 ∧ D 1=0 ∧ (D 0/D 2)=I := by
  intro p D
  let L := rhombicPeriodPair t hp
  let B := TraceData.slopingFluxCell188.plusTheta.output.toBall TraceData.slopingFluxDataSetup.config.prec
  obtain ⟨ht',hq,ha',hc,hv⟩ := sloping_flux_root_parameter_enclosures ht ha
  have disk := (TraceData.slopingFluxCell188.kernel_enclosures slopingFluxAnalyticSetup slopingFluxAnalyticSetup_valid
    TraceData.slopingFluxParams TraceData.slopingFluxWeight.output (s:=1) ht' hq ha' hc hv (by norm_num) (by norm_num)
    TraceData.slopingFluxCell188_checked).1
  have neg : originalPeriodPath t 1= -p := by dsimp [originalPeriodPath,p]; ring
  have per := thetaA_add_lattice hp a (-p) ⟨1+I*t,L.ω₂_mem_lattice⟩
  change thetaA t a (-p+(1+I*t))=thetaA t a (-p) at per
  rw [show -p+(1+I*t)=p by dsimp [p]; ring] at per
  have mem : B.interpret.Contains (thetaA t a p) := by
    rw [neg,← per] at disk
    exact disk
  have proj := (Complex.abs_im_le_norm (thetaA t a p-B.interpret.center.val)).trans mem
  change |(thetaA t a p).im-(B.center.im:ℝ)|≤(B.radius:ℝ) at proj
  have bd : (B.center.im:ℝ)+B.radius< -3 := by exact_mod_cast last_sloping_upper_bound
  have im : (thetaA t a p).im< -3 := by linarith [(abs_le.mp proj).2]
  have zero : D 1=0 := by
    change I*1/2*(thetaA t a p-thetaA t a (-p))=0
    rw [per,sub_self,mul_zero]
  have first : D 0= -thetaA t a p := by
    change -(1:ℂ)/2*(thetaA t a (-p)+thetaA t a p)= -thetaA t a p
    rw [← per]
    ring
  have dp : 3<(D 0).im := by rw [first,neg_im]; linarith
  have rect : p∈complexOpenRect 0 1 0 t := by
    change p.re∈Ioo (0:ℝ) 1 ∧ p.im∈Ioo (0:ℝ) t
    simp only [p,div_ofNat_re,div_ofNat_im,add_re,add_im,one_re,one_im,I_mul_re,I_mul_im,ofReal_im,ofReal_re,neg_zero,add_zero,zero_add]
    exact ⟨⟨by norm_num,by norm_num⟩,⟨by linarith,by linarith⟩⟩
  have off := rhombic_horizontal_strip_not_mem hp rect.2
  have hd := actualComplexHeight_hasDerivAt (a:=a) (c:=1) hp off
  have pos : 0<(D 2).re := by
    change 0<(coordinateData t a 1 hp p 2).re
    rw [← hd.deriv]
    exact (actual_complex_height_univalent_quarter (a:=a) hp).1 p rect
  have null : (D 0)^2+(D 1)^2+(D 2)^2=0 := coordinateData_null hp ab off
  have sq : (D 0)^2=(I*D 2)^2 := by
    rw [mul_pow,I_sq,neg_one_mul]
    linear_combination null - (D 1)*zero
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp sq with same|negated
  · have re : 3<(D 2).re := by rwa [same,I_mul_im] at dp
    have nz : D 2≠0 := fun e => pos.ne' (congrArg Complex.re e)
    exact ⟨re,same,zero,by rw [same,mul_div_cancel_right₀ _ nz]⟩
  · rw [negated,neg_im,I_mul_im] at dp
    linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_half_period_tangent_orientation
