import TwoAxisHelicoid.HolomorphicBoundaryBarrier
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology InnerProductSpace
open scoped Topology ContDiff Manifold

theorem SurfaceHarmonicGerm.affine {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M} {u : M → ℝ}
    (harm : SurfaceHarmonicGerm u x) (A b : ℝ) : SurfaceHarmonicGerm (fun y => A*u y+b) x := by
  obtain ⟨F,hF,eq⟩ := harm
  have lin : ContDiff ℂ ω (fun z : ℂ => (A:ℂ)*z+(b:ℂ)) := by fun_prop
  refine ⟨fun y => (A:ℂ)*F y+(b:ℂ),lin.contMDiff.contMDiffAt.comp x hF,?_⟩
  filter_upwards [eq] with y hy using by simp [hy,Complex.mul_re]

theorem SurfaceHarmonicGerm.add {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M} {u v : M → ℝ}
    (hu : SurfaceHarmonicGerm u x) (hv : SurfaceHarmonicGerm v x) : SurfaceHarmonicGerm (fun y => u y+v y) x := by
  obtain ⟨f,hf,ef⟩ := hu
  obtain ⟨g,hg,eg⟩ := hv
  refine ⟨fun y => f y+g y,hf.add hg,?_⟩
  filter_upwards [ef,eg] with y hy hy' using by simp only [hy,hy',Complex.add_re]

theorem SurfaceSubharmonicAt.affine_pos {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M}
    {u : M → ℝ} (sub : SurfaceSubharmonicAt u x) {A : ℝ} (ap : 0<A) (b : ℝ) :
    SurfaceSubharmonicAt (fun y => A*u y+b) x := by
  refine ⟨(continuousAt_const.mul sub.1).add continuousAt_const,?_⟩
  intro h hh mx
  let g := fun y => A⁻¹*h y+(-b/A)
  have hg : SurfaceHarmonicGerm g x := hh.affine A⁻¹ (-b/A)
  have iden (z : M) : A*(u z-g z)=A*u z+b-h z := by dsimp only [g]; field_simp; ring
  have m : IsLocalMax (fun y => u y-g y) x := by
    filter_upwards [mx] with z hz
    change A*u z+b-h z≤A*u x+b-h x at hz
    rwa [← iden,← iden,mul_le_mul_iff_right₀ ap] at hz
  filter_upwards [sub.2 g hg m] with z eq
  exact (iden z).symm.trans ((congrArg (fun a => A*a) eq).trans (iden x))

theorem surface_harmonic_log_distance {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {f : M → ℂ} {x : M} {c : ℂ} (hf : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f x) (ne : f x≠c) :
    SurfaceHarmonicGerm (fun y => Real.log ‖f y-c‖) x := by
  let e := chartAt ℂ x
  have xs : x∈e.source := mem_chart_source ℂ x
  have chart := IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) (n:=ω) x
  apply (surface_harmonic_germ_in_chart chart xs).mpr
  have back := contMDiffAt_symm_of_mem_maximalAtlas chart (e.map_source xs)
  have atx : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f (e.symm (e x)) := by rwa [e.left_inv xs]
  have an := ((atx.comp (e x) back).contDiffAt.analyticAt).sub (analyticAt_const (v:=c))
  exact an.harmonicAt_log_norm (sub_ne_zero.mpr (by simpa only [comp_apply,e.left_inv xs] using ne))

/-- On the annulus used for inserting a logarithmic pole, the
difference between its affine harmonic branch and the quadratic
subfunction changes sign exactly once, with the correct orientation. -/
theorem log_quadratic_seam_order : StrictAntiOn (fun s : ℝ => 1-s^2+Real.log s) (Ioi (3/4 : ℝ)) := by
  let f := fun s : ℝ => 1-s^2+Real.log s
  have der (t : ℝ) (h : 3/4<t) : HasDerivAt f (-(2*t)+t⁻¹) t := by
    have pos : 0<t := by linarith
    simpa [f,Pi.add_def,Pi.sub_def,Pi.pow_def] using (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).add (Real.hasDerivAt_log pos.ne'))
  apply strictAntiOn_of_deriv_neg (convex_Ioi _) (fun x hx => (der x hx).continuousAt.continuousWithinAt)
  intro x hx
  have lt : 3/4<x := interior_subset hx
  rw [(der x lt).deriv]
  have pos : 0<x := by linarith
  have bound : x⁻¹<2*x := by
    rw [← one_div,div_lt_iff₀ pos]
    nlinarith [sq_lt_sq₀ (by norm_num : (0:ℝ)≤3/4) pos.le |>.mpr lt]
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.log_quadratic_seam_order
