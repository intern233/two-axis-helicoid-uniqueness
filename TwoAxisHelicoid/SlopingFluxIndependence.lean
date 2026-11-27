import TwoAxisHelicoid.SlopingGeneratorFluxPlane
import TwoAxisHelicoid.ClosedDataQuantitativeFlux

namespace TwoAxisHelicoid
open Complex Matrix Set InnerProductSpace

/-- A nonzero first/third coordinate minor detects independent fluxes in
the actual three-dimensional ambient space. -/
theorem flux_pair_independent_of_minor {v w : Fin 3 → ℝ} (det : v 0*w 2-w 0*v 2≠0) :
    LinearIndependent ℝ ![v,w] := by
  apply LinearIndependent.pair_iff.mpr
  intro a b sum
  have zero (j : Fin 3) : a*v j+b*w j=0 := congrFun sum j
  have l (k : ℝ) (h : k*(v 0*w 2-w 0*v 2)=0) : k=0 := (mul_eq_zero.mp h).resolve_right det
  constructor
  · apply l a
    linear_combination w 2*zero 0-w 0*zero 2
  · apply l b
    linear_combination v 0*zero 2-v 2*zero 0

/-- Two linearly independent ambient flux vectors cannot both be
vertical in any invertible linear frame. -/
theorem independent_flux_pair_has_horizontal_component {v w : Fin 3 → ℝ}
    (ind : LinearIndependent ℝ ![v,w]) (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) :
    (∃ j : Fin 3, j≠2 ∧ T v j≠0) ∨ ∃ j : Fin 3, j≠2 ∧ T w j≠0 := by
  by_contra! h
  obtain ⟨v0,w0⟩ := h
  have z : (T w 2) • T v+ (-(T v 2)) • T w=0 := by
    funext j
    by_cases x : j=2
    · subst j
      change T w 2*T v 2+ (-(T v 2))*T w 2=0
      ring
    · change _*T v j+ _*T w j=0; rw [v0 j x,w0 j x]; ring
  have zero : (T w 2) • v+ (-(T v 2)) • w=0 := T.injective (by rw [map_add,map_smul,map_smul,map_zero]; exact z)
  obtain ⟨_,a⟩ := LinearIndependent.pair_iff.mp ind _ _ zero
  have van : T v=0 := by
    funext j
    by_cases k : j=2
    · subst j
      exact neg_eq_zero.mp a
    · exact v0 j k
  exact (ind.ne_zero 0) (show v=0 from T.injective (van.trans T.map_zero.symm))

/-- The image of the flux homomorphism of any closed basic torus
contains two independent vectors. Each vector consists of the three
conormal arclength integrals along a single genuine closed loop. -/
theorem closed_basic_immersion_two_independent_fluxes {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    (X : PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
    (reg : ∀ z∉(rhombicPeriodPair t ht).lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback _ X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback _ X) z)
    (hd : HasTwoAxisHelicoidCoordinateDifferential (puncturedTorusPullback _ X) t a c ht) :
    let L := rhombicPeriodPair t ht
    ∃ v w : Fin 3 → ℝ, LinearIndependent ℝ ![v,w] ∧
      (∃ (q : PuncturedPeriodTorus L) (γ : Path q q), ∀ j, TorusSpatialConormalIntegral L X j γ (v j)) ∧
      ∃ (q : PuncturedPeriodTorus L) (δ : Path q q), ∀ j, TorusSpatialConormalIntegral L X j δ (w j) := by
  obtain ⟨hG,_⟩ := periodic_actual_primitive_period_equations ht ha hc hd
    (fun z _ w hw => puncturedTorusPullback_periodic _ X z w hw)
  have non := (closed_basic_data_sloping_bound ht ha hc X hd).trans_lt (by norm_num : -(1/32:ℝ)<0)
  exact ⟨_,_,flux_pair_independent_of_minor (sloping_generator_flux_minor_ne_zero ht ha hc hG non.ne),sloping_generator_spatial_fluxes ht X reg hd⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.closed_basic_immersion_two_independent_fluxes
