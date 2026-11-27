import TwoAxisHelicoid.EvenMeromorphicDoublePole
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace TwoAxisHelicoid
open Complex Set Metric Filter MeasureTheory
open scoped Topology

/-- A genuine double pole has zero residue if arbitrarily small actual
circles around it have vanishing complex period. The regular part and
the nonzero leading coefficient are obtained from the local meromorphic
order alone. -/
theorem double_pole_principal_part_of_zero_circle_periods {h : ℂ → ℂ} (mer : MeromorphicAt h 0)
    (order : meromorphicOrderAt h 0=(-2:ℤ))
    (period : ∀ R : ℝ, 0<R → ∃ r∈Ioo (0:ℝ) R, (∮ z in C(0,r), h z)=0) :
    ∃ (A : ℂ) (P : ℂ → ℂ), A≠0 ∧ AnalyticAt ℂ P 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), h z=A/z^2+P z := by
  obtain ⟨u,an,unit,fac⟩ := (meromorphicOrderAt_eq_int_iff mer).mp order
  let A := u 0
  let B := deriv u 0
  let P := dslope (dslope u 0) 0
  have pa : AnalyticAt ℂ P 0 := analyticAt_dslope_center (analyticAt_dslope_center an)
  have expansion : ∀ᶠ z in 𝓝[≠] (0:ℂ), h z=A/z^2+B/z+P z := by
    filter_upwards [fac,self_mem_nhdsWithin] with z hz nz
    change z≠0 at nz
    have h0 : h z=u z/z^2 := by simpa [sub_zero,smul_eq_mul,zpow_neg,div_eq_mul_inv,mul_comm] using hz
    rw [h0]
    have a := sub_smul_dslope u 0 z
    have b := sub_smul_dslope (dslope u 0) 0 z
    simp only [sub_zero,smul_eq_mul,dslope_same] at a b
    dsimp only [A,B,P]
    field_simp [nz]
    linear_combination -a-z*b
  obtain ⟨R,rp,sub⟩ := Metric.mem_nhdsWithin_iff.mp (expansion.and (pa.eventually_analyticAt.filter_mono nhdsWithin_le_nhds))
  obtain ⟨r,hr,zero⟩ := period R rp
  have reg (z : ℂ) (hz : z∈ball (0:ℂ) R) : AnalyticAt ℂ P z := by
    by_cases e : z=0
    · exact e ▸ pa
    · exact (sub ⟨hz,e⟩).2
  have on (z : ℂ) (hz : z∈sphere (0:ℂ) r) : z∈ball (0:ℂ) R ∧ z≠0 := by
    have eq : ‖z‖=r := by simpa only [mem_sphere,dist_zero_right] using hz
    exact ⟨by simpa [mem_ball,dist_zero_right,eq] using hr.2,norm_pos_iff.mp (eq ▸ hr.1)⟩
  let J := fun z => wedgeIntegral 0 z P
  have pd : DifferentiableOn ℂ P (ball 0 R) := fun z hz => (reg z hz).differentiableAt.differentiableWithinAt
  let f := fun z : ℂ => A/z^2+P z
  let g := fun z : ℂ => B*z⁻¹
  have prim (z : ℂ) (hz : z∈sphere (0:ℂ) r) : HasDerivAt (fun w : ℂ => -A/w+J w) (f z) z := by
    have a : HasDerivAt (fun w : ℂ => -A/w) (A/z^2) z := by
      simpa using! (hasDerivAt_const z (-A)).div (hasDerivAt_id z) (on z hz).2
    exact a.add (pd.isConservativeOn.hasDerivAt_wedgeIntegral pd.continuousOn (on z hz).1)
  have cf : ContinuousOn f (sphere 0 r) := fun z hz =>
    ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero _ (on z hz).2)).add
      (reg z (on z hz).1).continuousAt).continuousWithinAt
  have cg : ContinuousOn g (sphere 0 r) := fun z hz =>
    (continuousAt_const.mul (continuousAt_id.inv₀ (on z hz).2)).continuousWithinAt
  have integral : (∮ z in C(0,r), h z)=(∮ z in C(0,r), f z+g z) := by
    apply circleIntegral.integral_congr hr.1.le
    intro z hz
    rw [(sub (on z hz)).1]
    dsimp [f,g]
    ring
  have first : (∮ z in C(0,r), f z)=0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.1.le (fun z hz => (prim z hz).hasDerivWithinAt)
  have invInt : (∮ z in C(0,r), z⁻¹)=2*Real.pi*I := by simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0:ℂ) hr.1.ne'
  rw [circleIntegral.integral_add (cf.circleIntegrable hr.1.le) (cg.circleIntegrable hr.1.le),first,zero_add] at integral
  change (∮ z in C(0,r), h z)=(∮ z in C(0,r), B*z⁻¹) at integral
  rw [circleIntegral.integral_const_mul,invInt,zero] at integral
  have bn : (2*(Real.pi:ℂ)*I)≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have b0 := (mul_eq_zero.mp integral.symm).resolve_right bn
  exact ⟨A,P,unit,pa,by simpa only [b0,zero_div,add_zero] using expansion⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.double_pole_principal_part_of_zero_circle_periods
