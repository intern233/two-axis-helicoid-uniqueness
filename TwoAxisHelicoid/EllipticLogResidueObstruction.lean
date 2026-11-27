import TwoAxisHelicoid.EllipticSimplePole
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- A finite meromorphic order gives the actual residue of its logarithmic
derivative, with a holomorphic remainder. The value at the puncture can
be assigned arbitrarily. -/
theorem meromorphic_log_derivative_residue_at_zero {f : ℂ → ℂ} {n : ℤ}
    (hf : MeromorphicAt f 0) (ho : meromorphicOrderAt f 0 = n) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv f z = (n:ℂ)/z + r z := by
  obtain ⟨u,hu,hn,he⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  have eq : f =ᶠ[𝓝[≠] (0:ℂ)] fun z => z^n*u z := by
    filter_upwards [he] with z hz using by simpa only [sub_zero,smul_eq_mul] using hz
  refine ⟨logDeriv u,hu.deriv.div hu hn,?_⟩
  filter_upwards [logDeriv_congr_nhdsNE eq,hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hu.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz ha hnu hne
  have nz : z ≠ 0 := hne
  have dp : DifferentiableAt ℂ (fun w : ℂ => w^n) z := differentiableAt_id.zpow (Or.inl nz)
  calc
    _ = logDeriv (fun w => w^n*u w) z := hz
    _ = logDeriv (fun w : ℂ => w^n) z+logDeriv u z := logDeriv_mul (f := fun w : ℂ => w^n) (g := u) z
      (zpow_ne_zero n nz) hnu dp ha.differentiableAt
    _ = _ := by rw [logDeriv_zpow]

/-- A doubly periodic function with a double and a simple principal part
at its only possible pole has zero coefficient of the simple part. -/
theorem elliptic_mixed_polar_residue_zero (L : PeriodPair) (f r : ℂ → ℂ) (A B : ℂ)
    (hf : AnalyticOnNhd ℂ f (L.lattice:Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z) (hr : AnalyticAt ℂ r 0)
    (he : ∀ᶠ z in 𝓝[≠] (0:ℂ), f z = A/z^2+B/z+r z) : B=0 := by
  let P := fun z => f z-A*L.weierstrassP z
  let E := fun z => r z-A*L.weierstrassPExcept 0 z
  apply elliptic_single_simple_pole_coefficient_zero L (f := P) (g := E)
    (fun z hz => (hf z hz).sub (analyticAt_const.mul (L.analyticOnNhd_weierstrassP z hz)))
    (fun z ω hω => by simp only [P,hp z ω hω,L.weierstrassP_add_coe z (⟨ω,hω⟩ : L.lattice)])
    (hr.sub (analyticAt_const.mul (L.analyticAt_weierstrassPExcept 0)))
  rw [eventually_nhdsWithin_iff] at he
  filter_upwards [he] with z hz
  intro hn
  have wp : L.weierstrassP z = L.weierstrassPExcept 0 z+1/z^2 := by
    simpa using (L.weierstrassPExcept_add (0 : L.lattice) z).symm
  rw [show P z = f z-A*L.weierstrassP z by rfl,hz hn,wp]
  dsimp [E]
  ring

/-- An actual holomorphic periodic coefficient whose log derivative has
a nonzero residue after removal of the double pole must have a zero off
the lattice. -/
theorem periodic_coefficient_has_zero_of_log_residue (L : PeriodPair) (f r : ℂ → ℂ) {A B : ℂ}
    (hf : AnalyticOnNhd ℂ f (L.lattice:Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z) (hr : AnalyticAt ℂ r 0)
    (he : ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv f z = A/z^2+B/z+r z)
    (hn : B ≠ 0) : ∃ z ∉ L.lattice, f z = 0 := by
  by_contra! hz
  apply hn
  apply elliptic_mixed_polar_residue_zero L (logDeriv f) r A B
    (fun z hw => (hf z hw).deriv.div (hf z hw) (hz z hw)) _ hr he
  intro z ω hω
  have e : (fun w => f (w+ω)) = f := funext fun w => hp w ω hω
  have d := deriv_comp_add_const f ω z
  rw [e] at d
  simp only [logDeriv_apply,hp z ω hω,← d]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.meromorphic_log_derivative_residue_at_zero
#print axioms TwoAxisHelicoid.periodic_coefficient_has_zero_of_log_residue
