import TwoAxisHelicoid.CertifiedHeightExtremalPair
import TwoAxisHelicoid.ExplicitEmbeddedAxes
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped ComplexConjugate

/-- The half-turn supplies the opposite extremal height in the same
certified immersion. If any double point is off the central plane, an
absolute-height maximum occurs at regular height on both sheets with
parallel horizontal Gauss directions. The two real saddles never coincide. -/
theorem certified_double_point_height_alternatives (fails : ¬ IsClosedEmbedding certifiedTorusImmersion) :
    let p := certifiedClosedParameters
    let L := certifiedPeriodPair
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let critical := fun u => fderiv ℝ (fun w => X w 2) u=0
    let G := thetaGauss p.t p.a 1
    ∃ z w : ℂ, z∉L.lattice ∧ w∉L.lattice ∧ periodTorusProjection L z≠periodTorusProjection L w ∧ X z=X w ∧
      (∀ u v, u∉L.lattice → v∉L.lattice → periodTorusProjection L u≠periodTorusProjection L v → X u=X v →
        |X u 2-X 1 2|≤X z 2-X 1 2) ∧ ¬ (critical z ∧ critical w) ∧
      (X z 2=X 1 2 ∨ (X 1 2<X z 2 ∧ ¬critical z ∧ ¬critical w ∧ (conj (G z)*G w).im=0)) := by
  let p := certifiedClosedParameters
  let L := certifiedPeriodPair
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have M := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  have diff : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun u hu => (M.2.2.2 u hu).1
  have S := explicit_centered_primitive_reflections p.height_pos diff M.1
  obtain ⟨z,w,hz,hw,ne,eq,upper,directions⟩ := certified_nonembedded_height_extremal_pair fails
  have absBound (u v : ℂ) (hu : u∉L.lattice) (hv : v∉L.lattice)
      (different : periodTorusProjection L u≠periodTorusProjection L v) (same : X u=X v) :
      |X u 2-X 1 2| ≤ X z 2-X 1 2 := by
    have U := (S u hu).1
    have V := (S v hv).1
    have eqsub : X (-u)-X 1=X (-v)-X 1 := by
      dsimp only at U V
      exact U.trans (by rw [same]; exact V.symm)
    have reflected := sub_left_inj.mp eqsub
    have other : periodTorusProjection L (-u)≠periodTorusProjection L (-v) := by
      intro h
      apply different
      apply (periodTorusProjection_eq_iff L u v).mpr
      have e := (periodTorusProjection_eq_iff L (-u) (-v)).mp h
      simpa only [neg_sub_neg,neg_sub] using L.lattice.neg_mem e
    have low := upper (-u) (-v) (by simpa using hu) (by simpa using hv) other reflected
    change X (-u) 2≤X z 2 at low
    have axis : X (-u) 2-X 1 2= -(X u 2-X 1 2) := congrFun U 2
    exact abs_le.mpr ⟨by linarith,sub_le_sub_right (upper u v hu hv different same) _⟩
  have saddle (u : ℂ) (hu : u∉L.lattice) (crit : fderiv ℝ (fun w => X w 2) u=0) : X u 2=X 1 2 := by
    obtain ⟨a,ha,_,_,same⟩ := actual_height_saddle_axis_representative p.height_pos p.abscissa_mem
      (one_ne_zero : (1:ℝ)≠0) diff M.1 hu crit
    exact (congrFun same 2).trans (actual_primitive_horizontal_line p.height_pos diff ha).2
  have oneSaddle := distinct_height_saddles_separated p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) diff M.1 hz hw ne
  refine ⟨z,w,hz,hw,ne,eq,absBound,fun both => oneSaddle both.1 both.2 eq,?_⟩
  by_cases zero : X z 2=X 1 2
  · exact Or.inl zero
  have pos : X 1 2<X z 2 := by
    have bound := absBound z w hz hw ne eq
    exact lt_of_le_of_ne (by linarith [abs_nonneg (X z 2-X 1 2)]) (Ne.symm zero)
  have rz := fun c => zero (saddle z hz c)
  have rw' := fun c => zero ((congrFun eq 2).trans (saddle w hw c))
  refine Or.inr ⟨pos,rz,rw',?_⟩
  have cz := (actual_height_critical_iff p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) diff hz).mpr
  have cw := (actual_height_critical_iff p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) diff hw).mpr
  rcases directions with a | a | a | a | target
  · exact (rz (cz (Or.inl a))).elim
  · exact (rz (cz (Or.inr a))).elim
  · exact (rw' (cw (Or.inl a))).elim
  · exact (rw' (cw (Or.inr a))).elim
  · exact target

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_double_point_height_alternatives
