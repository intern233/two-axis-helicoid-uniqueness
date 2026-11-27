import TwoAxisHelicoid.PeriodTorusTopology
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace TwoAxisHelicoid
open Set Complex Metric Filter Topology InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

/-- A height smooth away from one exceptional value can be replaced by a
globally smooth periodic height agreeing with its centered value near the
entire selected level. This permits complete plane flows even when the
punctured marking does not give a smooth chart at the filled point. -/
theorem periodic_cutoff_near_selected_height (L : PeriodPair) {h : ℂ → ℝ}
    (ch : Continuous h) (per : ∀ z w, w∈L.lattice → h (z+w)=h z)
    {bad v : ℝ} (distinct : v≠bad) (sm : ∀ z, h z≠bad → ContDiffAt ℝ ∞ h z) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ (∀ z w, w∈L.lattice → f (z+w)=f z) ∧
      ∀ z, h z=v → f =ᶠ[𝓝 z] (fun u => h u-v) := by
  let R := dist bad v
  have rp : 0<R := dist_pos.mpr distinct.symm
  let b : ContDiffBump v := ⟨R/4,R/2,by positivity,by linarith⟩
  let f := fun z => b (h z)*(h z-v)
  refine ⟨f,contDiff_iff_contDiffAt.mpr ?_,fun z w hw => by simp [f,per z w hw],?_⟩
  · intro z
    by_cases hz : h z=bad
    · have less : R/2<dist (h z) v := by rw [hz]; change R/2<R; linarith
      have continuousDistance : Continuous (fun y => dist (h y) v) := ch.dist continuous_const
      have near : ∀ᶠ y in 𝓝 z, R/2<dist (h y) v :=
        continuousDistance.continuousAt.tendsto.eventually (Ioi_mem_nhds less)
      apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [near] with y hy
      exact (by simp [f,b.zero_of_le_dist hy.le])
    · exact (b.contDiff.contDiffAt.comp z (sm z hz)).mul ((sm z hz).sub contDiffAt_const)
  · intro z hz
    have cv : Tendsto h (𝓝 z) (𝓝 v) := by rw [← hz]; exact ch.continuousAt
    have eq := b.eventuallyEq_one.comp_tendsto cv
    filter_upwards [eq] with y hy
    change b (h y)=1 at hy
    simp [f,hy]

/-- A trajectory of the rotated gradient preserves its Hamiltonian. -/
theorem rotated_gradient_preserves_height {f : ℂ → ℝ} (df : Differentiable ℝ f)
    {γ : ℝ → ℂ} (ode : ∀ t, HasDerivAt γ (I*gradient f (γ t)) t) :
    ∀ t, f (γ t)=f (γ 0) := by
  have rate (t : ℝ) : HasDerivAt (f ∘ γ) 0 t := by
    have d := (df (γ t)).hasFDerivAt.comp_hasDerivAt t (ode t)
    rw [← inner_gradient_left] at d
    have eq : ⟪gradient f (γ t),I*gradient f (γ t)⟫_ℝ=0 := real_inner_I_smul_self ℂ _
    rwa [eq] at d
  exact fun t => is_const_of_deriv_eq_zero (fun z => (rate z).differentiableAt) (fun z => (rate z).deriv) t 0

/-- When the centered height agrees near each point of a level with an
invariant scalar function, the entire connected orbit stays in that same
height level, even if the cutoff vanishes on other components. -/
theorem connected_orbit_preserves_selected_height {h f : ℂ → ℝ} {v : ℝ} {γ : ℝ → ℂ}
    (ch : Continuous h) (cg : Continuous γ) (start : h (γ 0)=v)
    (near : ∀ z, h z=v → f =ᶠ[𝓝 z] (fun u => h u-v))
    (invariant : ∀ t, f (γ t)=f (γ 0)) : ∀ t, h (γ t)=v := by
  let A := {t : ℝ | h (γ t)=v}
  have closed : IsClosed A := isClosed_eq (ch.comp cg) continuous_const
  have zero : f (γ 0)=0 := (near _ start).self_of_nhds.trans (show h (γ 0)-v=0 from sub_eq_zero.mpr start)
  have opened : IsOpen A := isOpen_iff_mem_nhds.mpr (by
    intro t ht
    filter_upwards [(near _ ht).comp_tendsto cg.continuousAt] with r hr
    change f (γ r)=h (γ r)-v at hr
    exact sub_eq_zero.mp (hr.symm.trans ((invariant r).trans zero)))
  have full := (show IsClopen A from ⟨closed,opened⟩).eq_univ (show A.Nonempty from ⟨0,start⟩)
  exact fun t => (show t∈A from full ▸ mem_univ _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_cutoff_near_selected_height
#print axioms TwoAxisHelicoid.rotated_gradient_preserves_height
#print axioms TwoAxisHelicoid.connected_orbit_preserves_selected_height
