import TwoAxisHelicoid.TorusAbelianPeriodLattice
import TwoAxisHelicoid.PlaneOrientationJacobian

namespace TwoAxisHelicoid
open Complex Set Function Topology
open scoped Topology ContDiff Manifold

/-- In period coordinates every sufficiently large ellipse encloses
the whole fiber. The image of its boundary winds once around the
specified value. The radius estimate uses the same bounded displacement
constant for every value. -/
theorem bounded_period_displacement_degree_one {D : ℂ → ℂ} (cont : Continuous D)
    (E : ℂ ≃L[ℝ] ℂ) {B : ℝ} (bound : ∀ z, ‖D z-E z‖≤B) (c : ℂ) {r : ℝ} (large : B+‖c‖<r) :
    (∀ z, D z=c → ‖E z‖<r) ∧ HasOrientationCircleDegree
      (fun a => planeOrientationDirection (D (E.symm (r • orientationRay a))-c)) 1 := by
  have bn : 0≤B := (norm_nonneg _).trans (bound 0)
  have rp := (add_nonneg bn (norm_nonneg c)).trans_lt large
  let q := fun a => r • orientationRay a
  have cq : Continuous q := orientationRay_continuous.const_smul r
  have nr (a : OrientationCircle) : ‖q a‖=r := by
    simp only [q,norm_smul,Real.norm_of_nonneg rp.le,orientationRay_norm,mul_one]
  constructor
  · intro z hz
    have h := bound z
    rw [hz,norm_sub_rev] at h
    calc
      ‖E z‖ = ‖(E z-c)+c‖ := by rw [sub_add_cancel]
      _ ≤ ‖E z-c‖+‖c‖ := norm_add_le _ _
      _ < r := (add_le_add h (le_refl ‖c‖)).trans_lt large
  · apply circle_degree_small_perturbation ((cont.comp (E.symm.continuous.comp cq)).sub continuous_const) cq
    · simp only [q,planeOrientationDirection_scaled_ray rp]
      exact orientationCircle_degree_id
    · intro a
      have h := bound (E.symm (q a))
      rw [E.apply_symm_apply] at h
      rw [nr]
      calc
        ‖D (E.symm (q a))-c-q a‖ = ‖(D (E.symm (q a))-q a)-c‖ := by congr 1; abel
        _ ≤ ‖D (E.symm (q a))-q a‖+‖c‖ := norm_sub_le _ _
        _ < r := (add_le_add h (le_refl ‖c‖)).trans_lt large

namespace HolomorphicCoefficientDisks

theorem torus_abelian_integral_has_boundary_degree_one {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [CompactSpace M] {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L)
    (A : HolomorphicCoefficientDisks M) (compat : A.compatibleOneForm) {x : M} (nonzero : A.coefficient x (chartAt ℂ x x)≠0) :
    let p := mark.symm ∘ periodTorusProjection L
    ∃ (D : ℂ → ℂ) (E : ℂ ≃L[ℝ] ℂ) (B : ℝ), A.IsAbelianIntegral p D ∧ IsProperMap D ∧
      (∀ z period, period∈L.lattice → D (z+period)=D z+E period) ∧
      ∀ (c : ℂ) {r : ℝ}, B+‖c‖<r → (∀ z, D z=c → ‖E z‖<r) ∧ HasOrientationCircleDegree
        (fun a => planeOrientationDirection (D (E.symm (r • orientationRay a))-c)) 1 := by
  obtain ⟨D,E,B,dev,prop,bound,inc,_⟩ := abelian_integral_full_period_lattice mark A compat nonzero
  exact ⟨D,E,B,dev,prop,inc,fun c _ hr => bounded_period_displacement_degree_one prop.continuous E bound c hr⟩

end HolomorphicCoefficientDisks
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.torus_abelian_integral_has_boundary_degree_one
