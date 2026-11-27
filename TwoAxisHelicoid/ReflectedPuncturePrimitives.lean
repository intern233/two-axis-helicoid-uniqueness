import TwoAxisHelicoid.PuncturedDifferentialResidue
import TwoAxisHelicoid.ArbitraryTorusHeightPole
import TwoAxisHelicoid.SpatialAxisGermDifferentials

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology InnerProductSpace
open scoped Topology ComplexConjugate

theorem HasPunctureResidue.congr {f g : ℂ → ℂ} {c : ℂ} (r : HasPunctureResidue f c)
    (eq : f=ᶠ[𝓝[≠] (0:ℂ)] g) : HasPunctureResidue g c := by
  obtain ⟨F,d⟩ := r
  exact ⟨F,(d.and eq).mono (fun z h => h.2 ▸ h.1)⟩

theorem HasPunctureResidue.reflected_negative {f : ℂ → ℂ} {c : ℂ} (r : HasPunctureResidue f c) :
    HasPunctureResidue (fun z => -conj (f (conj z))) (-conj c) := by
  obtain ⟨F,d⟩ := r
  refine ⟨fun z => -conj (F (conj z)),?_⟩
  filter_upwards [conjugation_tendsto_punctured_origin.eventually d] with z dz
  have der := dz.conj_conj.neg
  rw [starRingEnd_self_apply] at der
  convert der using 1
  · rfl
  · rw [map_sub,map_div₀,starRingEnd_self_apply,neg_div]
    ring

/-- A harmonic function odd under a reflection through a conformal
puncture has no logarithmic term. Its genuine complex potential is
single-valued and its real part is exactly the given height. -/
theorem reflected_odd_harmonic_has_end_primitive {y : ℂ → ℝ} {u : ℂ → ℂ}
    (harm : ∀ᶠ z in 𝓝[≠] (0:ℂ), HarmonicAt y z) (ua : AnalyticAt ℂ u 0) (uz : u 0=0) (un : deriv u 0≠0)
    (odd : (y ∘ u)=ᶠ[𝓝[≠] (0:ℂ)] fun z => -y (conj z)) :
    ∃ H : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (scalarComplexCoefficient y z) z ∧ (H z).re=y z := by
  let f := scalarComplexCoefficient y
  have realPart : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasFDerivAt y (realCoefficientDerivative (f z)) z :=
    harm.mono (fun _ hy => scalarComplexCoefficient_hasFDerivAt (hy.1.differentiableAt two_ne_zero))
  obtain ⟨c,res⟩ := exists_puncture_residue (f := f) (harm.mono fun _ h => (scalarComplexCoefficient_analyticAt h).differentiableAt)
  have tu : Tendsto u (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by simpa only [uz] using ua.differentiableAt.hasDerivAt.tendsto_nhdsNE un
  have eq : (fun z => deriv u z*f (u z))=ᶠ[𝓝[≠] (0:ℂ)] fun z => -conj (f (conj z)) := by
    filter_upwards [tu.eventually realPart,conjugation_tendsto_punctured_origin.eventually realPart,
      ua.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,punctured_germ_eventually_local odd] with z dy dc du germ
    have left : HasFDerivAt (y ∘ u) (realCoefficientDerivative (deriv u z*f (u z))) z := by
      convert dy.comp z (du.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ) using 1
      ext v
      change (v*(deriv u z*f (u z))).re=((v*deriv u z)*f (u z)).re
      rw [mul_assoc]
    have cc := dc.comp z Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
    rw [realCoefficientDerivative_conjugation] at cc
    have right : HasFDerivAt (fun w => -y (conj w)) (realCoefficientDerivative (-conj (f (conj z)))) z := by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using! real_primitive_scalar_mul_derivative cc (-1)
    exact realCoefficientDerivative_injective ((left.congr_of_eventuallyEq germ.symm).unique right)
  have e : c= -conj c := ((res.pullback ua uz un).congr eq).unique res.reflected_negative
  have zero : c=0 := by
    apply Complex.ext
    · have h := congrArg Complex.re e
      simp only [neg_re,conj_re] at h
      change c.re=0
      linarith
    · exact res.real_of_real_primitive realPart
  obtain ⟨F,dF⟩ := res
  have df : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (f z) z := by simpa only [zero,zero_div,sub_zero] using dF
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhdsWithin_iff.mp (df.and realPart)
  let V := {z : ℂ | 0<‖z‖ ∧ ‖z‖<r}
  have op : IsOpen V := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have data (z : ℂ) (hz : z∈V) := sub (show z∈ball (0:ℂ) r ∩ {0}ᶜ from
    ⟨by simpa only [mem_ball,dist_zero_right] using hz.2,norm_pos_iff.mp hz.1⟩)
  have dRe (z : ℂ) (hz : z∈V) : HasFDerivAt (fun w => (F w).re) (realCoefficientDerivative (f z)) z :=
    Complex.reCLM.hasFDerivAt.comp z ((data z hz).1.hasFDerivAt.restrictScalars ℝ)
  obtain ⟨b,same⟩ := op.exists_eq_add_of_fderiv_eq (complex_open_annulus_isPreconnected (r := 0) (R := r) le_rfl)
    (fun z hz => (data z hz).2.differentiableAt.differentiableWithinAt) (fun z hz => (dRe z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (data z hz).2.fderiv.trans (dRe z hz).fderiv.symm)
  refine ⟨fun z => F z+(b:ℂ),?_⟩
  filter_upwards [df,self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) rp)] with z hf nz small
  exact ⟨hf.add_const _,(same (show z∈V from ⟨norm_pos_iff.mpr nz,by simpa only [mem_ball,dist_zero_right] using small⟩)).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.reflected_odd_harmonic_has_end_primitive
