import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- On an outgoing coordinate ray a solution of u'=au with a≥0
cannot approach zero in positive time unless it vanishes on the tail.
The proof uses the actual squared coordinate. -/
theorem vanishing_tail_of_nondecreasing_amplitude {u a : ℝ → ℝ} (lim : Tendsto u atTop (𝓝 0))
    (event : ∀ᶠ t in atTop, HasDerivAt u (a t*u t) t ∧ 0≤a t) : ∀ᶠ t in atTop, u t=0 := by
  obtain ⟨T,after⟩ := eventually_atTop.mp event
  let f := fun t => (u t)^2
  have df (t : ℝ) (ht : T≤t) : HasDerivAt f (2*a t*(u t)^2) t := by
    convert! (after t ht).1.pow 2 using 1
    ring
  have inc : MonotoneOn f (Ici T) := monotoneOn_of_deriv_nonneg (convex_Ici _)
    (fun t ht => (df t ht).continuousAt.continuousWithinAt)
    (fun t ht => (df t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      have hT : T≤t := interior_subset ht
      rw [(df t hT).deriv]
      exact mul_nonneg (mul_nonneg (by norm_num) (after t hT).2) (sq_nonneg _))
  have l : Tendsto f atTop (𝓝 0) := by simpa only [zero_pow (by decide : 2≠0)] using lim.pow 2
  filter_upwards [eventually_ge_atTop T] with t ht
  have bound : f t≤0 := ge_of_tendsto l ((eventually_ge_atTop t).mono fun s h => inc ht (ht.trans h) h)
  exact sq_eq_zero_iff.mp (le_antisymm bound (sq_nonneg _))

theorem vanishing_negative_tail_of_nonincreasing_amplitude {u a : ℝ → ℝ} (lim : Tendsto u atBot (𝓝 0))
    (event : ∀ᶠ t in atBot, HasDerivAt u (a t*u t) t ∧ a t≤0) : ∀ᶠ t in atBot, u t=0 := by
  have eq := tendsto_neg_atTop_atBot.eventually event
  have reversed : ∀ᶠ t in atTop, HasDerivAt (fun s : ℝ => u (-s)) ((-a (-t))*u (-t)) t ∧ 0≤-a (-t) := by
    filter_upwards [eq] with t ht
    refine ⟨?_,neg_nonneg.mpr ht.2⟩
    convert! ht.1.comp t (hasDerivAt_neg t) using 1
    ring
  have result := vanishing_tail_of_nondecreasing_amplitude (lim.comp tendsto_neg_atTop_atBot) reversed
  simpa only [Function.comp_apply,neg_neg] using tendsto_neg_atBot_atTop.eventually result

/-- For a homoclinic Hamiltonian curve of a product saddle one end is
horizontal and the other vertical, in the very same coordinate chart.
The sign of its Jacobian decides the assignment of the ends. -/
theorem two_saddle_ends_on_different_axes {u v J : ℝ → ℝ} {j : ℝ} (nz : j≠0)
    (uTop : Tendsto u atTop (𝓝 0)) (uBot : Tendsto u atBot (𝓝 0))
    (vTop : Tendsto v atTop (𝓝 0)) (vBot : Tendsto v atBot (𝓝 0))
    (pos : ∀ᶠ t in atTop, 0<j*J t ∧ HasDerivAt u ((-J t)*u t) t ∧ HasDerivAt v (J t*v t) t)
    (neg : ∀ᶠ t in atBot, 0<j*J t ∧ HasDerivAt u ((-J t)*u t) t ∧ HasDerivAt v (J t*v t) t) :
    ((∀ᶠ t in atTop, v t=0) ∧ ∀ᶠ t in atBot, u t=0) ∨
      ((∀ᶠ t in atTop, u t=0) ∧ ∀ᶠ t in atBot, v t=0) := by
  rcases lt_or_gt_of_ne nz with small|large
  · right
    constructor
    · apply vanishing_tail_of_nondecreasing_amplitude (a:=fun t => -J t) uTop
      filter_upwards [pos] with t ht
      exact ⟨ht.2.1,neg_nonneg.mpr (neg_of_mul_pos_right ht.1 small.le).le⟩
    · apply vanishing_negative_tail_of_nonincreasing_amplitude vBot
      filter_upwards [neg] with t ht
      exact ⟨ht.2.2,(neg_of_mul_pos_right ht.1 small.le).le⟩
  · left
    constructor
    · apply vanishing_tail_of_nondecreasing_amplitude vTop
      filter_upwards [pos] with t ht
      exact ⟨ht.2.2,(pos_of_mul_pos_right ht.1 large.le).le⟩
    · apply vanishing_negative_tail_of_nonincreasing_amplitude (a:=fun t => -J t) uBot
      filter_upwards [neg] with t ht
      exact ⟨ht.2.1,neg_nonpos.mpr (pos_of_mul_pos_right ht.1 large.le).le⟩

/-- A nonzero coordinate tending to zero on a continuous tail can be
cut at any sufficiently small prescribed absolute radius. The sign of
the cut is recorded with the actual coordinate. -/
theorem radial_cuts_on_real_tail {u : ℝ → ℝ} {T : ℝ} (cu : ContinuousOn u (Ici T))
    (lim : Tendsto u atTop (𝓝 0)) :
    ∀ r∈Ioo 0 |u T|, ∃ t sign : ℝ, T≤t ∧ |sign|=1 ∧ u t=sign*r := by
  intro r hr
  have small : ∀ᶠ t in atTop, |u t|<r :=
    (continuous_abs.continuousAt.tendsto.comp lim).eventually (Iio_mem_nhds (by simpa using hr.1))
  obtain ⟨s,ss,ts⟩ := (small.and (eventually_ge_atTop T)).exists
  obtain ⟨t,ht,hit⟩ := intermediate_value_Icc' ts ((continuous_abs.comp_continuousOn cu).mono
    (fun _ h => h.1)) (show r∈Icc |u s| |u T| from ⟨ss.le,hr.2.le⟩)
  change |u t|=r at hit
  by_cases hp : 0≤u t
  · exact ⟨t,1,ht.1,abs_one,by simpa [abs_of_nonneg hp] using hit⟩
  · refine ⟨t,-1,ht.1,by norm_num,?_⟩
    rw [abs_of_neg (lt_of_not_ge hp)] at hit
    linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.two_saddle_ends_on_different_axes
#print axioms TwoAxisHelicoid.radial_cuts_on_real_tail
