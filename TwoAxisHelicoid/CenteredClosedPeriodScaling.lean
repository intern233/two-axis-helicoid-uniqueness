import TwoAxisHelicoid.CenteredActualImmersion
import TwoAxisHelicoid.CoordinatePrimitiveUniqueness

namespace TwoAxisHelicoid
open Set Topology

/-- Subtracting the value at the axis intersection removes the integration
constant. The centered maps then agree pointwise up to their signed scale
on the same punctured torus. -/
theorem centered_closed_torus_scale {t a c : ℝ} (ht : 0<t)
    (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0) (v : thetaG t a=0)
    (h : thetaHorizontalPeriod t a=0) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    centeredActualTorusImmersion ht ha hc v h q =
      c • centeredActualTorusImmersion ht ha one_ne_zero v h q := by
  let L := rhombicPeriodPair t ht
  obtain ⟨b,point⟩ := actual_coordinate_primitives_unique_up_to_scale_translation
    (X:=centeredActualPrimitive t a 1 ht) (Y:=centeredActualPrimitive t a c ht) ht one_ne_zero
    (fun _ hz => centeredActualPrimitive_hasFDerivAt ht ha one_ne_zero v h hz)
    (fun _ hz => centeredActualPrimitive_hasFDerivAt ht ha hc v h hz)
  have off : (1:ℂ)∉L.lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  have zero : b=0 := by simpa [centeredActualPrimitive] using (point 1 off).symm
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
  have proj : periodTorusProjection L z=q.1 := hz
  have reg : z∉L.lattice := fun member => q.2 (proj.symm.trans ((periodTorusProjection_eq_zero L z).mpr member))
  unfold centeredActualTorusImmersion
  rw [← proj]
  change centeredActualPrimitive t a c ht z=c • centeredActualPrimitive t a 1 ht z
  simpa only [div_one,zero,add_zero] using point z reg

/-- A closed unit-scale period solution that embeds at the unit scale
embeds at every nonzero signed scale on its punctured parameter torus. -/
theorem centered_closed_embedding_all_scales {t a c : ℝ} (ht : 0<t)
    (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0) (v : thetaG t a=0) (h : thetaHorizontalPeriod t a=0)
    (unitInj : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      actualTorusImmersion ht ha one_ne_zero v h q.1)) :
    IsClosedEmbedding (centeredActualTorusImmersion ht ha hc v h) := by
  have proper := centeredActualTorusImmersion_isProperMap ht ha hc v h
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap proper.continuous _ proper.isClosedMap
  intro x y eqn
  rw [centered_closed_torus_scale ht ha hc v h x,centered_closed_torus_scale ht ha hc v h y] at eqn
  apply unitInj
  exact sub_left_inj.mp ((smul_right_injective _ hc) eqn)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centered_closed_torus_scale
#print axioms TwoAxisHelicoid.centered_closed_embedding_all_scales

