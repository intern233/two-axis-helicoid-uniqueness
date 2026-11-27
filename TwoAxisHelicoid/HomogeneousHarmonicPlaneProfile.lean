import TwoAxisHelicoid.RadialProfileLaplacian
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Harmonic.Analytic

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff InnerProductSpace Laplacian

/-- A nonzero homogeneous harmonic function of positive integer degree
on the real plane has exactly the angular profile of a complex monomial. -/
theorem homogeneous_harmonic_plane_profile {P : ℂ → ℝ} {n : ℕ} (pos : 0<n)
    (harm : ∀ v, HarmonicAt P v) (hom : ∀ r : ℝ, ∀ v, P (r • v)=r^n*P v) (nz : ∃ v, P v≠0) :
    ∃ C : ℂ, C≠0 ∧ ∀ z, P z=(C*z^n).re := by
  have h0 : P 0=0 := by simpa only [zero_smul,zero_pow pos.ne',zero_mul] using hom 0 0
  obtain ⟨F,an,rePart⟩ := (show HarmonicOnNhd P univ from fun v _ => harm v).exists_analyticOnNhd_univ_re_eq
  let G := fun z : ℂ => F z-F 0
  have ag : AnalyticOnNhd ℂ G univ := an.sub analyticOnNhd_const
  have g0 : G 0=0 := sub_self _
  have realG (z : ℂ) : (G z).re=P z := by
    change (F z-F 0).re=P z
    rw [Complex.sub_re,congrFun rePart z,congrFun rePart 0,h0,sub_zero]
  have realScaling (r : ℝ) : ∀ z : ℂ, G ((r:ℂ)*z)=(r:ℂ)^n*G z := by
    let J := fun z : ℂ => G ((r:ℂ)*z)-(r:ℂ)^n*G z
    have aj : AnalyticOnNhd ℂ J univ := fun z _ => ((ag _ (mem_univ _)).comp
      (analyticAt_const.mul analyticAt_id)).sub (analyticAt_const.mul (ag z (mem_univ z)))
    have vanishes (z : ℂ) (_ : z∈(univ:Set ℂ)) : (J z).re=0 := by
      change (G ((r:ℂ)*z)-(r:ℂ)^n*G z).re=0
      rw [Complex.sub_re,← Complex.ofReal_pow,Complex.re_ofReal_mul,realG,realG,← Complex.real_smul,hom,sub_self]
    obtain ⟨k,val⟩ := aj.eq_const_of_re_eq_const vanishes isOpen_univ isConnected_univ
    have jk : J 0=0 := by simp only [J,mul_zero,g0,sub_self]
    intro z
    apply sub_eq_zero.mp
    exact (val z (mem_univ _)).trans ((val 0 (mem_univ _)).symm.trans jk)
  have realLine (r : ℝ) : G (r:ℂ)=G 1*(r:ℂ)^n := by simpa only [mul_one,mul_comm ((r:ℂ)^n)] using realScaling r 1
  have embed : Tendsto (fun r : ℝ => (r:ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_ofReal.continuousWithinAt,?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact Complex.ofReal_ne_zero.mpr (show r≠0 from hr)
  have all : G=(fun z : ℂ => G 1*z^n) := ag.eq_of_frequently_eq (analyticOnNhd_const.mul (analyticOnNhd_id.pow n))
    (embed.frequently ((Eventually.of_forall realLine).frequently))
  have eq (z : ℂ) : P z=(G 1*z^n).re := (realG z).symm.trans (congrArg Complex.re (congrFun all z))
  obtain ⟨v,hv⟩ := nz
  exact ⟨G 1,fun h => hv (by rw [eq,h,zero_mul,Complex.zero_re]),eq⟩

/-- Centering and cutting off an analytic germ supplies a smooth
global representative agreeing on an actual ball around its center. -/
private theorem smooth_analytic_germ_representative {f : ℂ → ℝ} {x : ℂ} (an : AnalyticAt ℝ f x) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp an.eventually_analyticAt
  let b : ContDiffBump x := ⟨r/4,r/2,by positivity,by linarith⟩
  refine ⟨fun z => b z*f z,contDiff_iff_contDiffAt.mpr (fun z => ?_),?_⟩
  · by_cases hz : z∈tsupport b
    · rw [b.tsupport_eq] at hz
      exact b.contDiff.contDiffAt.mul ((sub ((Metric.closedBall_subset_ball
        (show b.rOut<r by dsimp [b]; linarith)) hz)).contDiffAt)
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with z az
      change b z=0 at az
      simp only [az,zero_mul]
  · filter_upwards [b.eventuallyEq_one] with z hz
    change b z=1 at hz
    simp only [hz,one_mul]

/-- The full order of an analytic tangent intersection is detected in
the actual conformal plane. The quotient by the radial power is smooth
jointly in radius and direction, including radius zero. -/
theorem analytic_drift_germ_radial_normal_form {f A B : ℂ → ℝ} {x : ℂ}
    (an : AnalyticAt ℝ f x) (zero : f x=0) (flat : fderiv ℝ f x=0)
    (nonzero : ¬ f =ᶠ[𝓝 x] 0) (ca : ContinuousAt A x) (cb : ContinuousAt B x)
    (pde : ∀ᶠ z in 𝓝 x, (Δ f) z=A z*planePartial 1 f z+B z*planePartial I f z) :
    ∃ (n : ℕ) (C : ℂ) (H : ℝ × ℂ → ℝ) (R : ℝ), 2≤n ∧ C≠0 ∧ 0<R ∧
      ContDiff ℝ ∞ H ∧ (∀ v, H (0,v)=(C*v^n).re) ∧
      ∀ r v, ‖r • v‖<R → f (x+r • v)=r^n*H (r,v) := by
  obtain ⟨g,sg,eg⟩ := smooth_analytic_germ_representative an
  have nz : ¬ g =ᶠ[𝓝 x] 0 := fun eq => nonzero (eg.symm.trans eq)
  obtain ⟨n,H,lo,sh,witness,form⟩ := smooth_radial_leading_profile sg (eg.self_of_nhds.trans zero)
    (eg.fderiv_eq.trans flat) (an.congr eg.symm) nz
  have force : ∀ᶠ z in 𝓝 x, (Δ g) z=A z*planePartial 1 g z+B z*planePartial I g z := by
    filter_upwards [laplacian_congr_nhds eg,eg.fderiv (𝕜:=ℝ),pde] with z hl hd hz
    simpa only [planePartial,hd,hl] using hz
  obtain ⟨harm,hom⟩ := radial_profile_harmonic_homogeneous sg ca cb force sh form
  obtain ⟨C,cn,angular⟩ := homogeneous_harmonic_plane_profile (by omega : 0<n) harm hom witness
  obtain ⟨R,rp,agree⟩ := Metric.mem_nhds_iff.mp eg
  refine ⟨n,C,H,R,lo,cn,rp,sh,angular,?_⟩
  intro r v small
  exact (agree (show x+r • v∈Metric.ball x R by simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left] using small)).symm.trans (form r v)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.homogeneous_harmonic_plane_profile
#print axioms TwoAxisHelicoid.analytic_drift_germ_radial_normal_form
