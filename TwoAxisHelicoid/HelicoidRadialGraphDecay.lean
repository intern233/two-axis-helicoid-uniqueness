import TwoAxisHelicoid.HelicoidGraphDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

namespace TwoAxisHelicoid
open Filter Bornology Real Set
open scoped Topology

theorem helicoid_graph_radial_derivative_bound (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) :
    |fderiv ℝ u q (1,0)| ≤ helicoidGraphGradientNorm u q := by
  let x := fderiv ℝ u q (1,0)
  let y := fderiv ℝ u q (0,1)
  have hy : 0≤y^2/(helicoidQ q.1)^2 := by positivity
  change |x|≤sqrt (x^2+y^2/(helicoidQ q.1)^2)
  rw [← Real.sqrt_sq_eq_abs x]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right hy)

/-- Decay of the induced graph gradient controls the signed normal
height divided by the ruling parameter uniformly, including near the
two remote parts of the vertical axis. -/
theorem helicoid_graph_height_small_relative_to_radius {u : ℝ × ℝ → ℝ}
    (diff : ∀ᶠ q in cobounded (ℝ × ℝ), DifferentiableAt ℝ u q)
    (decay : Tendsto (fun q => |u q|+helicoidGraphGradientNorm u q) (cobounded (ℝ × ℝ)) (𝓝 0))
    (axis : ∀ᶠ θ in cobounded ℝ, u (0,θ)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in cobounded (ℝ × ℝ), |u q|≤ε*|q.1| := by
  have small : ∀ᶠ q in cobounded (ℝ × ℝ), |u q|+helicoidGraphGradientNorm u q<ε := decay (eventually_lt_nhds hε)
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp (diff.and small)
  obtain ⟨B,_,hB⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp axis
  apply Filter.hasBasis_cobounded_norm.eventually_iff.mpr
  refine ⟨max (max R B) 1+1,trivial,?_⟩
  intro q hq
  change max (max R B) 1+1≤‖q‖ at hq
  have bigR : R ≤ ‖q‖ := by linarith [le_max_left R B,le_max_left (max R B) 1]
  have grad0 (p : ℝ × ℝ) : 0 ≤ helicoidGraphGradientNorm u p := Real.sqrt_nonneg _
  by_cases radius : 1≤|q.1|
  · have su := (hR bigR).2
    exact (show |u q|≤ε by linarith [grad0 q]).trans (le_mul_of_one_le_right hε.le radius)
  have eq : ‖q‖=|q.2| := by
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
    apply max_eq_right
    by_contra! hh
    have hnorm : ‖q‖=|q.1| := by rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_eq_left hh.le]
    rw [hnorm] at hq
    linarith [le_max_right (max R B) 1]
  have large (x : ℝ) : R ≤ ‖(x,q.2)‖ := by
    change R ≤ max |x| |q.2|
    exact (bigR.trans_eq eq).trans (le_max_right _ _)
  have hzero : u (0,q.2)=0 := hB (by change B ≤ |q.2|; rw [← eq]; linarith [le_max_right R B,le_max_left (max R B) 1])
  let f := fun x : ℝ => u (x,q.2)
  let d := fun x : ℝ => fderiv ℝ u (x,q.2) (1,0)
  have deriv' (x : ℝ) : HasDerivAt f (d x) x :=
    (hR (large x)).1.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x q.2))
  have bounded (x : ℝ) : ‖d x‖≤ε := by
    have su := (hR (large x)).2
    have rd := helicoid_graph_radial_derivative_bound u (x,q.2)
    change |fderiv ℝ u (x,q.2) (1,0)|≤ε
    linarith [abs_nonneg (u (x,q.2))]
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (deriv' x).hasDerivWithinAt) (fun x _ => bounded x) (mem_univ (0:ℝ)) (mem_univ q.1)
  simpa only [f,Prod.eta,hzero,sub_zero,Real.norm_eq_abs] using h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_graph_height_small_relative_to_radius
