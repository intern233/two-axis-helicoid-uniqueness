import TwoAxisHelicoid.PuncturePrimitiveResidue
import TwoAxisHelicoid.PrimitiveDoublePoleExpansion
import TwoAxisHelicoid.ResidueFreeDoublePoleChange
import TwoAxisHelicoid.RealCoefficientSymmetry
import TwoAxisHelicoid.AntiholomorphicChartGerms

namespace TwoAxisHelicoid
open Complex Set Filter Metric MeasureTheory Topology
open scoped Topology ComplexConjugate

/-- The residue of a holomorphic differential on a punctured disk is
characterized by a single-valued primitive after subtracting c dz/z.
The singularity may be essential. -/
def HasPunctureResidue (f : ℂ → ℂ) (c : ℂ) : Prop :=
  ∃ F : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (f z-c/z) z

theorem exists_puncture_residue {f : ℂ → ℂ} (hol : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z) :
    ∃ c, HasPunctureResidue f c := by
  obtain ⟨r,rp,all⟩ := Metric.mem_nhdsWithin_iff.mp hol
  obtain ⟨c,F,d⟩ := puncture_primitive_modulo_log rp (fun z n s => all
    (show z∈ball (0:ℂ) r ∩ {0}ᶜ from ⟨by simpa only [mem_ball,dist_zero_right] using s,norm_pos_iff.mp n⟩))
  refine ⟨c,F,?_⟩
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) rp)] with z nz near
  exact d z (norm_pos_iff.mpr nz) (by simpa only [mem_ball,dist_zero_right] using near)

/-- A single-valued real or complex potential on a punctured disk
cannot have a nonzero constant angular derivative around its circles. -/
theorem constant_angular_derivative_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℂ → E} {c : E} (diff : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∃ A : ℂ →L[ℝ] E, HasFDerivAt F A z ∧ A (z*I)=c) : c=0 := by
  obtain ⟨r,rp,all⟩ := Metric.mem_nhdsWithin_iff.mp diff
  let γ := circleMap (0:ℂ) (r/2)
  have rad (t : ℝ) : ‖γ t‖=r/2 := (norm_circleMap_zero _ _).trans (abs_of_pos (half_pos rp))
  have d (t : ℝ) : HasDerivAt (F ∘ γ) c t := by
    obtain ⟨A,h,v⟩ := all (show γ t∈ball (0:ℂ) r ∩ {0}ᶜ from
      ⟨by rw [mem_ball,dist_zero_right,rad]; exact half_lt_self rp,norm_pos_iff.mp ((rad t).symm ▸ half_pos rp)⟩)
    exact v ▸ h.comp_hasDerivAt t (hasDerivAt_circleMap 0 (r/2) t)
  have period : γ (2*Real.pi)=γ 0 := by simp [γ,circleMap,Complex.exp_two_pi_mul_I]
  have calcInt := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.two_pi_pos.le
    (fun t _ => (d t).continuousAt.continuousWithinAt) (fun t _ => d t) (intervalIntegrable_const (b := 2*Real.pi) (μ := volume))
  rw [intervalIntegral.integral_const,sub_zero,Function.comp_apply,Function.comp_apply,period,sub_self] at calcInt
  exact (smul_eq_zero.mp calcInt).resolve_left Real.two_pi_pos.ne'

theorem HasPunctureResidue.unique {f : ℂ → ℂ} {a b : ℂ} (pa : HasPunctureResidue f a)
    (pb : HasPunctureResidue f b) : a=b := by
  obtain ⟨F,dF⟩ := pa
  obtain ⟨G,dG⟩ := pb
  have zero : (b-a)*I=0 := by
    apply constant_angular_derivative_zero (F := fun z => F z-G z)
    filter_upwards [dF,dG,self_mem_nhdsWithin] with z hf hg nz
    refine ⟨_,(hf.sub hg).hasFDerivAt.restrictScalars ℝ,?_⟩
    change (z*I)*(f z-a/z-(f z-b/z))=(b-a)*I
    field_simp [show z≠0 from nz]
    ring
  exact (sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_right I_ne_zero)).symm

theorem HasPunctureResidue.real_of_real_primitive {y : ℂ → ℝ} {f : ℂ → ℂ} {c : ℂ}
    (res : HasPunctureResidue f c)
    (realPart : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasFDerivAt y (realCoefficientDerivative (f z)) z) : c.im=0 := by
  obtain ⟨F,dF⟩ := res
  have zero : -c.im=0 := by
    apply constant_angular_derivative_zero (F := fun z => y z-(F z).re)
    filter_upwards [dF,realPart,self_mem_nhdsWithin] with z hf hy nz
    refine ⟨_,hy.sub (reCLM.hasFDerivAt.comp z (hf.hasFDerivAt.restrictScalars ℝ)),?_⟩
    change ((z*I)*(f z)).re-((z*I)*(f z-c/z)).re= -c.im
    rw [← sub_re,show (z*I)*(f z)-(z*I)*(f z-c/z)=c*I by field_simp [show z≠0 from nz]; ring]
    simp
  exact neg_eq_zero.mp zero

theorem HasPunctureResidue.pullback {f u : ℂ → ℂ} {c : ℂ} (res : HasPunctureResidue f c)
    (hu : AnalyticAt ℂ u 0) (uz : u 0=0) (non : deriv u 0≠0) :
    HasPunctureResidue (fun z => deriv u z*f (u z)) c := by
  let a := dslope u 0
  have ha : AnalyticAt ℂ a 0 := analyticAt_dslope_center hu
  have na : a 0≠0 := (dslope_same _ _).trans_ne non
  have factor (z : ℂ) : z*a z=u z := by simpa [a,uz,smul_eq_mul] using sub_smul_dslope u 0 z
  let g := fun w => deriv a w/a w
  have hg : AnalyticAt ℂ g 0 := ha.deriv.div ha na
  obtain ⟨r,rp,good⟩ := Metric.mem_nhds_iff.mp hg.eventually_analyticAt
  have hd : DifferentiableOn ℂ g (ball 0 r) := fun z hz => (good hz).differentiableAt.differentiableWithinAt
  let P := fun z => wedgeIntegral 0 z g
  have dp (z : ℂ) (hz : z∈ball 0 r) : HasDerivAt P (g z) z := hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn hz
  obtain ⟨F,dF⟩ := res
  have tu : Tendsto u (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by simpa only [uz] using hu.differentiableAt.hasDerivAt.tendsto_nhdsNE non
  refine ⟨fun z => F (u z)+c*P z,?_⟩
  filter_upwards [tu.eventually dF,ha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (ha.continuousAt.eventually_ne na).filter_mono nhdsWithin_le_nhds,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) rp),
    self_mem_nhdsWithin] with z df aa az small nz
  have du : HasDerivAt u (a z+z*deriv a z) z := by
    simpa only [← funext factor,one_mul,id_eq] using! (hasDerivAt_id z).mul aa.differentiableAt.hasDerivAt
  have combined := (df.comp z du).add ((dp z small).const_mul c)
  convert combined using 1
  · rfl
  · rw [du.deriv,← factor z]
    change (a z+z*deriv a z)*f (z*a z)-c/z=(f (z*a z)-c/(z*a z))*(a z+z*deriv a z)+c*(deriv a z/a z)
    field_simp [show z≠0 from nz,az]
    ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasPunctureResidue.unique
#print axioms TwoAxisHelicoid.HasPunctureResidue.real_of_real_primitive
#print axioms TwoAxisHelicoid.HasPunctureResidue.pullback
