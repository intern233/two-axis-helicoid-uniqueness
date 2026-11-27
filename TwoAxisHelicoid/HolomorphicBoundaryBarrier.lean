import TwoAxisHelicoid.SurfaceHarmonicComparison
import TwoAxisHelicoid.PerronHarmonicReplacement

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology InnerProductSpace
open scoped Topology ContDiff Manifold

theorem SurfaceSubharmonicAt.congr_germ {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {x : M}
    {f g : M → ℝ} (hf : SurfaceSubharmonicAt f x) (eq : g =ᶠ[𝓝 x] f) : SurfaceSubharmonicAt g x := by
  refine ⟨hf.1.congr_of_eventuallyEq eq,?_⟩
  intro h hh hx
  have loc : IsLocalMax (fun y => f y-h y) x := by
    filter_upwards [eq,hx] with y hy mx
    change f y-h y≤f x-h x
    simpa only [hy,eq.self_of_nhds] using (show g y-h y≤g x-h x from mx)
  filter_upwards [eq,hf.2 h hh loc] with y hy he using by rwa [hy,eq.self_of_nhds]

theorem surface_harmonic_const {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (a : ℝ) (x : M) :
    SurfaceHarmonicGerm (fun _ => a) x := ⟨fun _ => (a:ℂ),contMDiffAt_const,.of_forall fun _ => rfl⟩

/-- Squared modulus has an affine harmonic support at each point
of a holomorphic coordinate. This proves intrinsic subharmonicity. -/
theorem surface_subharmonic_scaled_norm_sq {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {x : M} {f : M → ℂ} (hf : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f x)
    {A : ℝ} (pos : 0≤A) (b : ℝ) : SurfaceSubharmonicAt (fun y => A*(‖f y‖^2-b)) x := by
  let a := f x
  let G := fun y => (A:ℂ)*(2*(starRingEnd ℂ a)*f y-((‖a‖^2+b:ℝ):ℂ))
  have hg : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω G x := by
    have lin : ContDiff ℂ ω (fun z : ℂ => (A:ℂ)*(2*(starRingEnd ℂ a)*z-((‖a‖^2+b:ℝ):ℂ))) := by fun_prop
    exact lin.contMDiff.contMDiffAt.comp x hf
  have val (y : M) : (G y).re=A*(2*⟪a,f y⟫_ℝ-(‖a‖^2+b)) := by
    rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply']
    have a2 : (((‖a‖:ℝ):ℂ)^2).re=‖a‖^2 := by rw [← Complex.ofReal_pow,Complex.ofReal_re]
    simp [G,Complex.mul_re,Complex.mul_im,a2]
    ring_nf
    simp
  have low (y : M) : (G y).re≤A*(‖f y‖^2-b) := by
    rw [val]
    apply mul_le_mul_of_nonneg_left _ pos
    nlinarith [norm_sub_sq_real a (f y),sq_nonneg ‖a-f y‖]
  apply surface_subharmonic_of_touch_below
    ((show SurfaceHarmonicGerm (fun y => (G y).re) x from ⟨G,hg,.of_forall fun _ => rfl⟩).subharmonicAt)
    (continuousAt_const.mul ((hf.continuousAt.norm.pow 2).sub continuousAt_const)) low
  change A*(‖f x‖^2-b)=(G x).re
  rw [val,show f x=a from rfl,real_inner_self_eq_norm_sq]
  ring

/-- Truncate a holomorphic barrier and extend it through a collar
on which it is already constant. Its extremal boundary limit is inherited
from the squared norm of the coordinate. -/
theorem truncated_coordinate_boundary_barrier {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (θ : M → ℝ) (ct : Continuous θ) {a b k : ℝ} (ab : a<b) (k1 : k<1)
    (f : M → ℂ) (hol : ∀ x, θ x<b → ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f x)
    (disk : ∀ x, θ x<b → ‖f x‖<1) (collar : ∀ x, a≤θ x → θ x<b → ‖f x‖^2≤k) :
    ∃ (B : M → ℝ) (A : ℝ), 0<A ∧ (∀ x, SurfaceSubharmonicAt B x) ∧
      (∀ x, -1≤B x ∧ B x<0) ∧ (∀ x, a≤θ x → B x= -1) ∧
      (∀ x, θ x<b → B x=max (-1) (A*(‖f x‖^2-1))) := by
  classical
  let A := (1-k)⁻¹
  have ap : 0<A := inv_pos.mpr (sub_pos.mpr k1)
  let h := fun x => A*(‖f x‖^2-1)
  let B := fun x => if θ x<b then max (-1) (h x) else -1
  have exterior (x : M) (hx : a≤θ x) : B x= -1 := by
    by_cases lt : θ x<b
    · rw [show B x=max (-1) (h x) from ite_eq_left lt,max_eq_left]
      change (1-k)⁻¹*(‖f x‖^2-1)≤ -1
      rw [inv_mul_eq_div,div_le_iff₀ (sub_pos.mpr k1)]
      linarith [collar x hx lt]
    · exact ite_eq_right lt
  refine ⟨B,A,ap,fun x => ?_,fun x => ?_,exterior,fun x hx => ite_eq_left hx⟩
  · by_cases lt : θ x<b
    · apply (surface_subharmonic_max ((surface_harmonic_const (-1) x).subharmonicAt)
        (surface_subharmonic_scaled_norm_sq (hol x lt) ap.le 1)).congr_germ
      filter_upwards [ct.continuousAt.eventually_lt continuousAt_const lt] with y hy using ite_eq_left hy
    · apply ((surface_harmonic_const (-1) x).subharmonicAt).congr_germ
      filter_upwards [continuousAt_const.eventually_lt ct.continuousAt (ab.trans_le (le_of_not_gt lt))] with y hy using exterior y hy.le
  · by_cases lt : θ x<b
    · rw [show B x=max (-1) (h x) from ite_eq_left lt]
      refine ⟨le_max_left _ _,max_lt (by norm_num) (mul_neg_of_pos_of_neg ap (sub_neg.mpr ?_))⟩
      nlinarith [disk x lt,norm_nonneg (f x),sq_lt_sq₀ (norm_nonneg (f x)) (by norm_num : (0:ℝ)≤1) |>.mpr (disk x lt)]
    · rw [show B x= -1 from ite_eq_right lt]
      norm_num

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.truncated_coordinate_boundary_barrier
