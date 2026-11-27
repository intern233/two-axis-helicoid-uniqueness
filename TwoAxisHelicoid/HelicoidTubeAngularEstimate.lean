import TwoAxisHelicoid.HelicoidGraphAxisVanishing
import Mathlib.Analysis.Complex.Trigonometric

namespace TwoAxisHelicoid
open Set Filter Bornology Real

/-- The horizontal coordinate after rotating back by the actual
vertical coordinate of the spatial point. -/
noncomputable def tubeRelativeHorizontal (y : HelicoidTubeCoordinates) : ℂ :=
  let p := helicoidTubeRotation.symm y
  ⟨p.1.1,p.1.2⟩

theorem tubeRelativeHorizontal_exp (y : HelicoidTubeCoordinates) :
    tubeRelativeHorizontal y=Complex.exp (((-y.2:ℝ):ℂ)*Complex.I)*Complex.mk y.1.1 y.1.2 := by
  apply Complex.ext
  · change y.1.1*cos y.2+y.1.2*sin y.2=_
    rw [Complex.mul_re,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,cos_neg,sin_neg]
    dsimp only
    ring
  · change -y.1.1*sin y.2+y.1.2*cos y.2=_
    rw [Complex.mul_im,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,cos_neg,sin_neg]
    dsimp only
    ring

private theorem phase_bound (r s : ℝ) : |helicoidAngle r s| ≤ |s| := by
  have hr : |r|≤helicoidQ r := by nlinarith [helicoidQ_sq r,helicoidQ_pos r,sq_abs r]
  rw [helicoidAngle,abs_div,abs_mul,abs_of_pos (helicoidQ_pos r)]
  exact (div_le_iff₀ (helicoidQ_pos r)).mpr (mul_le_mul_of_nonneg_left hr (abs_nonneg _))

private theorem normal_div_bound (r s : ℝ) : |s/helicoidQ r|≤|s| := by
  rw [abs_div,abs_of_pos (helicoidQ_pos r)]
  exact div_le_self (abs_nonneg _) (helicoidQ_ge_one r)

theorem helicoid_normal_graph_angular_estimate (r θ s : ℝ) :
    let y := helicoidTubeMap ((s,r),θ)
    |(tubeRelativeHorizontal y).im|≤|r| * |s|+|s| ∧ |r|≤‖tubeRelativeHorizontal y‖ ∧ ‖y‖≤‖(r,θ)‖+|s| := by
  let y := helicoidTubeMap ((s,r),θ)
  have reduced : tubeRelativeHorizontal y=Complex.mk (helicoidU r s) (helicoidV r s) := by
    unfold tubeRelativeHorizontal
    rw [show helicoidTubeRotation.symm y=_ from helicoidTubeMap_reduced ((s,r),θ)]
  have small := normal_div_bound r s
  have component (a b : ℝ) (h : |b|≤1) : |a*b|≤|a| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h
  refine ⟨?_,?_,?_⟩
  · rw [reduced]
    change |-r*sin (helicoidAngle r s)-s/helicoidQ r*cos (helicoidAngle r s)|≤_
    apply (abs_sub _ _).trans
    apply add_le_add _ ((component _ _ (abs_cos_le_one _)).trans small)
    rw [abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs.trans (phase_bound r s)) (abs_nonneg _)
  · rw [reduced]
    have e : ‖Complex.mk (helicoidU r s) (helicoidV r s)‖^2=r^2+(s/helicoidQ r)^2 := by
      rw [← Complex.normSq_eq_norm_sq]
      change (helicoidU r s)*(helicoidU r s)+(helicoidV r s)*(helicoidV r s)=_
      dsimp only [helicoidU,helicoidV]
      linear_combination (r^2+(s/helicoidQ r)^2)*sin_sq_add_cos_sq (helicoidAngle r s)
    nlinarith [sq_abs r,sq_nonneg (s/helicoidQ r),norm_nonneg (Complex.mk (helicoidU r s) (helicoidV r s))]
  · have rb : |r|≤‖(r,θ)‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le (r,θ)
    have hb : |θ|≤‖(r,θ)‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le (r,θ)
    change max (max |r*cos θ+s/helicoidQ r*sin θ| |r*sin θ-s/helicoidQ r*cos θ|) |θ+helicoidAngle r s|≤_
    apply max_le (max_le _ _) _
    · exact (abs_add_le _ _).trans (add_le_add ((component _ _ (abs_cos_le_one _)).trans rb) ((component _ _ (abs_sin_le_one _)).trans small))
    · exact (abs_sub _ _).trans (add_le_add ((component _ _ (abs_sin_le_one _)).trans rb) ((component _ _ (abs_cos_le_one _)).trans small))
    · exact (abs_add_le _ _).trans (add_le_add hb (phase_bound r s))

/-- On the actual C¹ graph with the full vertical axis, the imaginary
part in the rotating frame is small relative to the horizontal radius
uniformly near infinity, even for points approaching the axis. -/
theorem helicoid_C1_end_relative_horizontal_small {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (cy : Continuous Y) (axis : ∀ θ : ℝ, ((0,0),θ) ∈ range Y)
    (endGraph : HasHelicoidC1End Y) (ε : ℝ) (hε : 0<ε) :
    ∃ A : ℝ, ∀ x : M, A≤‖Y x‖ → |(tubeRelativeHorizontal (Y x)).im|≤ε*‖tubeRelativeHorizontal (Y x)‖ := by
  obtain ⟨C,_,R,_,compact,E,_,u,smooth,graph,limit⟩ := endGraph
  obtain ⟨lim,relative⟩ := exterior_helicoid_graph_relative_radial_decay cy axis compact E smooth graph limit
  obtain ⟨B,bound⟩ := (compact.image cy).isBounded.exists_norm_le
  let v := extendOpenScalar u
  have small : ∀ᶠ q in cobounded (ℝ × ℝ), |v q|+helicoidGraphGradientNorm v q<ε/2 := lim (eventually_lt_nhds (half_pos hε))
  obtain ⟨D,_,hD⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp (small.and (relative (ε/2) (half_pos hε)))
  refine ⟨max B D+2,fun x hx => ?_⟩
  have inK : x ∈ helicoidProjectedEnd Y C (exteriorPlaneBase R) := by
    by_contra h
    have hb := bound _ (mem_image_of_mem Y h)
    linarith [le_max_left B D]
  let p := E ⟨x,inK⟩
  have pos : Y x=helicoidTubeMap ((u p,p.1.1),p.1.2) := by simpa only [p,E.symm_apply_apply] using (graph p).2
  have cert := helicoid_normal_graph_angular_estimate p.1.1 p.1.2 (u p)
  rw [← pos] at cert
  have db : D≤‖p.1‖ := by linarith [cert.2.2,(graph p).1,le_max_right B D]
  have s : |v p.1|+helicoidGraphGradientNorm v p.1<ε/2 ∧ |v p.1|≤ε/2*|p.1.1| := hD db
  have ev : v p.1=u p := by simp [v,extendOpenScalar,p.property]
  rw [ev] at s
  have nonneg : 0≤helicoidGraphGradientNorm v p.1 := Real.sqrt_nonneg _
  calc |(tubeRelativeHorizontal (Y x)).im| ≤ |p.1.1| * |u p|+|u p| := cert.1
    _ ≤ |p.1.1| * (ε/2)+(ε/2)*|p.1.1| := add_le_add (mul_le_mul_of_nonneg_left (by linarith [s.1]) (abs_nonneg _)) s.2
    _ = ε*|p.1.1| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left cert.2.1 hε.le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_C1_end_relative_horizontal_small
