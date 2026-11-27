import TwoAxisHelicoid.PuncturedDifferentialResidue
import TwoAxisHelicoid.PhysicalDifferentialHeightGerm
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace TwoAxisHelicoid
open Complex Set Metric Filter MeasureTheory Topology InnerProductSpace Laplacian
open scoped Topology

/-- The circle integral detects the residue of a holomorphic punctured
germ even if its isolated singularity is essential. -/
theorem HasPunctureResidue.small_circle_integrals {f : ℂ → ℂ} {a : ℂ}
    (res : HasPunctureResidue f a) (hol : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z) :
    ∃ R : ℝ, 0<R ∧ ∀ r∈Ioo (0:ℝ) R, (∮ z in C(0,r), f z)=a*(2*(Real.pi:ℂ)*I) := by
  obtain ⟨P,dP⟩ := res
  obtain ⟨R,Rp,good⟩ := Metric.mem_nhdsWithin_iff.mp (dP.and hol)
  refine ⟨R,Rp,?_⟩
  intro r hr
  have rad {z : ℂ} (hz : z∈sphere (0:ℂ) r) : ‖z‖=r := by
    simpa only [mem_sphere,dist_zero_right] using hz
  have inside {z : ℂ} (hz : z∈sphere (0:ℂ) r) : z∈ball (0:ℂ) R ∩ {0}ᶜ :=
    ⟨mem_ball_zero_iff.mpr ((rad hz).trans_lt hr.2),norm_pos_iff.mp ((rad hz).symm ▸ hr.1)⟩
  have F : CircleIntegrable f 0 r := ContinuousOn.circleIntegrable hr.1.le
    (fun z hz => (good (inside hz)).2.continuousAt.continuousWithinAt)
  have G : CircleIntegrable (fun z : ℂ => a/z) 0 r := ContinuousOn.circleIntegrable hr.1.le
    (fun z hz => (continuousAt_const.div continuousAt_id (inside hz).2).continuousWithinAt)
  have period : (∮ z in C(0,r), f z-a/z)=0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.1.le
      (fun z hz => (good (inside hz)).1.hasDerivWithinAt)
  have inv : (∮ z in C(0,r), z⁻¹)=2*(Real.pi:ℂ)*I := by
    simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0:ℂ) hr.1.ne'
  rw [circleIntegral.integral_sub F G] at period
  simpa only [div_eq_mul_inv,circleIntegral.integral_const_mul,inv] using sub_eq_zero.mp period

/-- For a single-valued harmonic coordinate only the imaginary circle
period remains to be tested. Its vanishing at arbitrarily small radii
gives the actual single-valued complex potential with the prescribed
real coordinate on a punctured neighborhood. -/
theorem harmonic_puncture_primitive_of_peripheral_flux {x : ℂ → ℝ}
    (harm : ∀ᶠ z in 𝓝[≠] (0:ℂ), HarmonicAt x z)
    (flux : ∀ ε : ℝ, 0<ε → ∃ r∈Ioo (0:ℝ) ε, (∮ z in C(0,r), scalarComplexCoefficient x z).im=0) :
    ∃ P : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt P (scalarComplexCoefficient x z) z ∧ (P z).re=x z := by
  let f := scalarComplexCoefficient x
  have hol : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z :=
    harm.mono (fun _ hz => (scalarComplexCoefficient_analyticAt hz).differentiableAt)
  obtain ⟨a,res⟩ := exists_puncture_residue hol
  have im := res.real_of_real_primitive (harm.mono (fun _ h => scalarComplexCoefficient_hasFDerivAt
    (h.1.differentiableAt two_ne_zero)))
  obtain ⟨R,Rp,circles⟩ := res.small_circle_integrals hol
  obtain ⟨r,hr,zero⟩ := flux R Rp
  have v := congrArg Complex.im (circles r hr)
  change (∮ z in C(0,r), f z).im=0 at zero
  rw [zero] at v
  have evaluate : (a*(2*(Real.pi:ℂ)*I)).im=a.re*(2*Real.pi) := by simp [Complex.mul_im,Complex.mul_re]
  have realPart : a.re=0 := (mul_eq_zero.mp (evaluate.symm.trans v.symm)).resolve_right (by positivity)
  have az : a=0 := Complex.ext realPart im
  obtain ⟨H,primitive⟩ := res
  have prim : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (f z) z := by simpa only [az,zero_div,sub_zero] using primitive
  obtain ⟨b,agree⟩ := punctured_height_equals_real_primitive ((harm.and prim).mono
    (fun _ a => ⟨a.1.1.differentiableAt two_ne_zero,rfl,a.2⟩))
  refine ⟨fun z => (b:ℂ)+H z,?_⟩
  filter_upwards [prim,agree] with z h p
  exact ⟨h.const_add _,by simpa using p.symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasPunctureResidue.small_circle_integrals
#print axioms TwoAxisHelicoid.harmonic_puncture_primitive_of_peripheral_flux
