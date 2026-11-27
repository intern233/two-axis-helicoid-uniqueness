import TwoAxisHelicoid.CompactRegularOrbitCircle
import TwoAxisHelicoid.EquivariantTorusFrame
import Mathlib.Analysis.Calculus.Deriv.Inverse

namespace TwoAxisHelicoid
open Set Complex Metric Filter Topology Function
open scoped Topology ContDiff

/-- A lifted plane curve with nonzero speed cannot return to its initial
quotient point at arbitrarily small positive times. -/
theorem nonzero_velocity_torus_period_gap (L : PeriodPair) {γ : ℝ → ℂ} {v : ℂ}
    (deriv : HasDerivAt γ v 0) (nz : v≠0) :
    ∃ d>0, ∀ t∈Ioo (0:ℝ) d, periodTorusProjection L (γ t)≠periodTorusProjection L (γ 0) := by
  obtain ⟨ε,pos,isolated⟩ := lattice_norm_isolated_zero L
  have small : ∀ᶠ t in 𝓝 (0:ℝ), ‖γ t-γ 0‖<ε :=
    (deriv.continuousAt.sub continuousAt_const).norm.eventually_lt_const (by simpa using pos)
  have away : ∀ᶠ t in 𝓝[≠] (0:ℝ), γ t≠γ 0 := deriv.eventually_ne nz
  have both := small.and (eventually_nhdsWithin_iff.mp away)
  obtain ⟨d,dp,inside⟩ := Metric.mem_nhds_iff.mp both
  refine ⟨d,dp,?_⟩
  intro t ht equal
  have pair := inside (show t∈ball (0:ℝ) d by simpa [Real.dist_eq,abs_of_pos ht.1] using ht.2)
  exact pair.2 ht.1.ne' (sub_eq_zero.mp (isolated _ ((periodTorusProjection_eq_iff L _ _).mp equal.symm) pair.1))

/-- Open time orbits on a compact level restrict to open orbits on its
individual connected components. Their primitive period parametrizations
take values in the actual component subtype. -/
theorem compact_level_component_orbit_circle {S : Type*} [TopologicalSpace S] [T2Space S]
    [CompactSpace S] (G : ℝ → S → S) (zero : ∀ x, G 0 x=x)
    (add : ∀ a b x, G (a+b) x=G a (G b x)) (cont : ∀ x, Continuous (fun t => G t x))
    (op : ∀ x, IsOpenMap (fun t => G t x)) (x : S)
    (gap : ∃ d>0, ∀ r∈Ioo (0:ℝ) d, G r x≠x) :
    ∃ T>0, ∃ e : OrientationCircle ≃ₜ connectedComponent x,
      ∀ t : ℝ, (e (t:OrientationCircle)).1=G (t*T) x := by
  let C := connectedComponent x
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let _ : ConnectedSpace C := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have stays (p : C) (t : ℝ) : G t p.1∈C := by
    have inOrbit := (isPreconnected_range (cont p.1)).subset_connectedComponent
      (show p.1∈range (fun r => G r p.1) from ⟨0,zero _⟩) (mem_range_self t)
    exact (show connectedComponent p.1⊆C from (connectedComponent_eq p.2).ge) inOrbit
  let F := fun t (q : C) => (⟨G t q.1,stays q t⟩:C)
  let p : C := ⟨x,mem_connectedComponent⟩
  obtain ⟨d,dp,dg⟩ := gap
  obtain ⟨T,tp,e,eq⟩ := compact_open_orbit_circle F p (fun q => Subtype.ext (zero _))
    (fun a b q => Subtype.ext (add a b _)) (fun q => (cont q.1).subtype_mk _)
    (fun q => (op q.1).codRestrict (stays q)) ⟨d,dp,fun t ht same => dg t ht (congrArg Subtype.val same)⟩
  exact ⟨T,tp,e,fun t => congrArg Subtype.val (eq t)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nonzero_velocity_torus_period_gap
#print axioms TwoAxisHelicoid.compact_level_component_orbit_circle
