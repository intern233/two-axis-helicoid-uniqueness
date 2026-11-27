import TwoAxisHelicoid.AnalyticFinitePeriodParameters
import TwoAxisHelicoid.PositivePitchRepresentative
import TwoAxisHelicoid.HarmonicAxisIntersectionPoint

namespace TwoAxisHelicoid
open Complex Set Filter Topology

/-- In the positive unit-pitch frame the two half turns fix the spatial
origin. Equal marked parameter therefore determines the actual map on
the whole punctured plane, including its translation. -/
theorem positive_pitch_positions_of_equal_parameter (U V : PitchNormalizedBasicImmersion)
    (u : U∈positiveUnitPitchFamily) (v : V∈positiveUnitPitchFamily) (same : U.t=V.t) :
    ∀ z∉(rhombicPeriodPair U.t U.ht).lattice, V.position z=U.position z := by
  have scale := V.scale
  rw [abs_of_neg v.2,← same] at scale
  have c : V.c=U.c := by
    have other := U.scale
    rw [abs_of_neg u.2] at other
    linarith
  have dv : HasTwoAxisHelicoidCoordinateDifferential V.position U.t (verticalA U.t) V.c U.ht := by
    simpa only [same] using V.differential
  obtain ⟨b,positions⟩ := actual_coordinate_primitives_unique_up_to_scale_translation U.ht u.2.ne U.differential dv
  obtain ⟨hu,_⟩ := u.1
  obtain ⟨hv,_⟩ := v.1
  have one : (1:ℂ)∉(rhombicPeriodPair U.t U.ht).lattice := by
    simpa using real_not_mem_rhombic_lattice_of_pos U.ht (by norm_num : (0:ℝ)<1) (by norm_num)
  have eb := positions 1 one
  rw [harmonic_axis_parameter_one V.ht hv,harmonic_axis_parameter_one U.ht hu,smul_zero,zero_add] at eb
  intro z hz
  simpa only [c,div_self u.2.ne,one_smul,← eb,add_zero] using positions z hz

/-- Every sequence in the fixed-axis, positive unit-pitch, nonperiodic
normalized family has a subsequence of exactly equal physical maps off
the puncture, in the same marking. The proof uses analytic endpoint
signs and the identity theorem, without a counted horizontal box. -/
theorem fixed_axis_positive_pitch_stationary_subsequence (x : ℕ → positiveUnitPitchFamily) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, (x (φ n)).1.t=(x (φ 0)).1.t ∧
      ∀ z∉(rhombicPeriodPair (x (φ 0)).1.t (x (φ 0)).1.ht).lattice,
        (x (φ n)).1.position z=(x (φ 0)).1.position z := by
  let Z := {t : ℝ | t∈Ioo 0 ellipticVerticalUpper ∧ actualPeriodAlong t=0}
  have member (n : ℕ) : (x n).1.t∈Z := by
    let W := (x n).1
    have sign : W.c<0 := (x n).2.2
    exact ⟨⟨W.ht,W.hT⟩,(periodic_actual_primitive_period_equations W.ht
      (verticalA_spec ⟨W.ht,W.hT⟩).1 sign.ne W.differential W.periodic).2⟩
  have often : ∃ᶠ n in atTop, ∃ t∈Z, (x n).1.t=t :=
    (Eventually.of_forall (fun n => ⟨_,member n,rfl⟩)).frequently
  obtain ⟨t,_,occurs⟩ := actualPeriodAlong_finite_zero_parameters_analytic.frequently_exists.mp often
  obtain ⟨φ,inc,stationary⟩ := extraction_of_frequently_atTop occurs
  refine ⟨φ,inc,fun n => ?_⟩
  have same := (stationary n).trans (stationary 0).symm
  exact ⟨same,positive_pitch_positions_of_equal_parameter _ _ (x (φ 0)).2 (x (φ n)).2 same.symm⟩

/-- In this normalization even the set of spatial images itself is
finite, before passing to similarity classes or using the global
certified period root. -/
theorem fixed_axis_positive_pitch_finite_images : (PitchNormalizedBasicImmersion.image '' positiveUnitPitchFamily).Finite := by
  classical
  let S := positiveUnitPitchFamily
  let R := PitchNormalizedBasicImmersion.t '' S
  have finite : R.Finite := actualPeriodAlong_finite_zero_parameters_analytic.subset (by
    rintro t ⟨W,hw,rfl⟩
    exact ⟨⟨W.ht,W.hT⟩,(periodic_actual_primitive_period_equations W.ht
      (verticalA_spec ⟨W.ht,W.hT⟩).1 hw.2.ne W.differential W.periodic).2⟩)
  let img := fun t : ℝ => if h : t∈R then h.choose.image else ∅
  apply (finite.image img).subset
  rintro _ ⟨W,hw,rfl⟩
  have hit : W.t∈R := ⟨W,hw,rfl⟩
  refine ⟨W.t,hit,?_⟩
  simp only [img,dite_eq_left hit]
  have hV := hit.choose_spec
  have eq := positive_pitch_positions_of_equal_parameter W hit.choose hw hV.1 hV.2.symm
  unfold PitchNormalizedBasicImmersion.image
  rw [show ((rhombicPeriodPair hit.choose.t hit.choose.ht).lattice : Set ℂ)ᶜ=
          ((rhombicPeriodPair W.t W.ht).lattice : Set ℂ)ᶜ by simp only [hV.2]]
  exact image_congr (fun z hz => congrArg coordinateToEuclidean (eq z hz))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positive_pitch_positions_of_equal_parameter
#print axioms TwoAxisHelicoid.fixed_axis_positive_pitch_stationary_subsequence
#print axioms TwoAxisHelicoid.fixed_axis_positive_pitch_finite_images
