import TwoAxisHelicoid.FixedAxisAnalyticCompactness
import TwoAxisHelicoid.TorusGeneratorIntersections
import TwoAxisHelicoid.SmoothGeneratingCoreTransfer

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

/-- The two affine lattice-basis lines through the center project to
the actual generators of the compact torus and avoid the puncture for
every real time. -/
noncomputable def basisSmoothGeneratingCurves (L : PeriodPair) : SmoothGeneratingTorusCurves L where
  base := periodBasisLine L 0 0
  loop i := (puncturedTorusGeneratorLoop L i).map continuous_subtype_val
  arc i := {
    left := 0, right := 1, ordered := zero_le_one
    curve := periodBasisLine L i, velocity := fun _ => L.basis i
    stays := fun s _ => periodBasisLine_not_mem_lattice L i s
    continuous_curve := (continuous_subtype_val.comp (puncturedBasisLine_continuous L i)).continuousOn
    continuous_velocity := continuousOn_const
    derivative := fun s _ => periodBasisLine_hasDerivAt L i s }
  left _ := rfl
  right _ := rfl
  start _ := by simp [periodBasisLine]
  projects _ _ := rfl
  generate := periodTorusFundamentalGroup_generated L

/-- The physical trajectories of the marked generators are smooth
on the whole parameter line. -/
theorem smooth_pitch_model_basis_curve (W : PitchNormalizedBasicImmersion) (mem : W∈embeddedPitchFamily)
    (i : Fin 2) : ContDiff ℝ ∞ (coordinateToEuclidean ∘ W.position ∘ periodBasisLine (rhombicPeriodPair W.t W.ht) i) := by
  let L := rhombicPeriodPair W.t W.ht
  obtain ⟨h,_⟩ := mem
  have line : ContDiff ℝ ∞ (periodBasisLine L i) := by unfold periodBasisLine; fun_prop
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have a : AnalyticAt ℝ W.position (periodBasisLine L i t) :=
    analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (h.harmonic _ (periodBasisLine_not_mem_lattice L i t) j))
  exact coordinateToEuclidean.contDiff.contDiffAt.comp t (a.contDiffAt.comp t line.contDiffAt)

/-- The precise smooth generating-core compactness used in the flux
argument is proved for the nonperiodic normalized candidates, using
the separate analytic finiteness of the scalar period zero set. -/
theorem fixed_axis_analytic_smooth_generating_curves : HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily := by
  intro x
  obtain ⟨φ,inc,stationary⟩ := fixed_axis_positive_pitch_stationary_subsequence x
  let W := fun n => (x (φ n)).1
  let L := fun n => rhombicPeriodPair (W n).t (W n).ht
  let P := fun n (i : Fin 2) => coordinateToEuclidean ∘ (W n).position ∘ periodBasisLine (L n) i
  have fixed (n : ℕ) (i : Fin 2) : P n i=P 0 i := by
    have ht : (W n).t=(W 0).t := (stationary n).1
    have lattice : L n=L 0 := by dsimp only [L]; simp only [ht]
    funext s
    change coordinateToEuclidean ((W n).position (periodBasisLine (L n) i s))=_
    rw [lattice]
    exact congrArg coordinateToEuclidean ((stationary n).2 _ (periodBasisLine_not_mem_lattice (L 0) i s))
  refine ⟨φ,inc,fun n => basisSmoothGeneratingCurves (L n),fun i => deriv (P 0 i),?_,?_⟩
  · intro i
    exact ((smooth_pitch_model_basis_curve (W 0) (x (φ 0)).2.1 i).continuous_deriv (by norm_num)).continuousOn
  · intro i u hu
    apply Eventually.of_forall
    intro n s _
    change (deriv (P 0 i) s,deriv (P n i) s)∈u
    rw [fixed n i]
    exact refl_mem_uniformity hu

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fixed_axis_analytic_smooth_generating_curves
