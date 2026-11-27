import TwoAxisHelicoid.SlopingCycleAxisCore
import TwoAxisHelicoid.SlopingAccelerationCover

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

/-- The two full generators of the certified torus give embedded horizontal
circles on opposite sides of the common axis plane, meeting exactly at the
projection of the crossing. The acceleration bound is supplied by the
kernel-checked theta-derivative enclosure. -/
theorem certified_sloping_cycles_horizontal_bouquet :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let P := originalPeriodPath p.t
    let H := fun z => (X z 0,X z 1)
    ∃ G J : AddCircle (2:ℝ) → ℝ × ℝ, IsClosedEmbedding G ∧ IsClosedEmbedding J ∧
      (∀ s∈Icc (-1:ℝ) 1, G (s:AddCircle (2:ℝ))=H (P s) ∧ J (s:AddCircle (2:ℝ))=H (conj (P s))) ∧
      range G ∩ range J={H 1} := by
  intro p X P H
  obtain ⟨t,a⟩ := certifiedClosedParameters_bounds
  apply sloping_cycles_horizontal_bouquet (Ioo_subset_Icc_self t) (Ioo_subset_Icc_self a) p.height_pos
    (X:=X) _ _ sloping_axis_positive_acceleration_cover
  · exact fun z hz => ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem
      (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  · exact actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed

/-- Joint spatial injectivity of both complete axes and both generator
loops of the certified torus. A compact set disjoint from their union
contains one endpoint of every remaining possible double point. -/
theorem certified_axis_and_cycle_injective_core :
    let p := certifiedClosedParameters
    let A := rhombicMarkedAxes p.t p.height_pos ∪ rhombicSlopingCycle p.height_pos false ∪ rhombicSlopingCycle p.height_pos true
    InjOn certifiedTorusImmersion A ∧ ∃ B K : Set (PuncturedPeriodTorus certifiedPeriodPair),
      IsCompact B ∧ IsCompact K ∧ B⊆K ∧ Disjoint A B ∧ InjOn certifiedTorusImmersion Bᶜ ∧
      (IsClosedEmbedding certifiedTorusImmersion ↔ ∀ x∈B, ∀ y∈K, certifiedTorusImmersion x=certifiedTorusImmersion y → x=y) :=
  certified_axis_and_cycle_injective_core_of_acceleration sloping_axis_positive_acceleration_cover

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_sloping_cycles_horizontal_bouquet
#print axioms TwoAxisHelicoid.certified_axis_and_cycle_injective_core
