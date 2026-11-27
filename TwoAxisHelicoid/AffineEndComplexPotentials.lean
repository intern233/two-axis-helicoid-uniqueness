import TwoAxisHelicoid.PhysicalReflectionCoordinatePrimitives
import TwoAxisHelicoid.UnmarkedPhysicalAxisPlacement

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ComplexConjugate ContDiff Manifold

/-- All Cartesian coordinates are real parts of genuine holomorphic
potentials around the puncture, with the correct actual differentials. -/
def HasEndCartesianPotentials (X : ℂ → Fin 3 → ℝ) : Prop :=
  ∀ j : Fin 3, ∃ H : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (immersionComplexCoefficient X z j) z ∧ (H z).re=X z j

/-- Exactness of the Cartesian differentials is intrinsic under any
real affine change of spatial coordinates, including signed dilations. -/
theorem HasEndCartesianPotentials.affine {X : ℂ → Fin 3 → ℝ} (h : HasEndCartesianPotentials X)
    (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ) :
    HasEndCartesianPotentials (fun z => L (X z)+b) := by
  classical
  choose H d using h
  intro j
  let c := fun i : Fin 3 => L (Pi.single i (1:ℝ)) j
  let G := fun z => (∑ i : Fin 3, (c i:ℂ)*H i z)+(b j:ℂ)
  have lin (v : Fin 3 → ℝ) : ∑ i, c i*v i=L v j := by
    have reconstruct : ∑ i, v i • Pi.single i (1:ℝ)=v := by
      ext k
      simp [Finset.sum_apply,Pi.single_apply]
    have eq := congrArg (fun t => L t j) reconstruct
    simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm,c] using eq
  have all := Filter.eventually_all.mpr d
  have val : ∀ᶠ z in 𝓝[≠] (0:ℂ), (G z).re=(L (X z)+b) j := by
    filter_upwards [all] with z hz
    simp only [G,add_re,Complex.re_sum,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,Pi.add_apply]
    simpa only [fun i => (hz i).2] using congrArg (fun v : ℝ => v+b j) (lin (X z))
  refine ⟨G,?_⟩
  filter_upwards [all,val,punctured_germ_eventually_local val] with z atz point eq
  have derivG : HasDerivAt G ((∑ i : Fin 3, (c i:ℂ)*immersionComplexCoefficient X z i)) z :=
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((atz i).1.const_mul _))).add_const _
  let y := fun w => (L (X w)+b) j
  have realDeriv : HasFDerivAt y (realCoefficientDerivative (∑ i : Fin 3, (c i:ℂ)*immersionComplexCoefficient X z i)) z :=
    (Complex.reCLM.hasFDerivAt.comp z (derivG.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq eq.symm
  have coeff := realCoefficientDerivative_injective ((scalarComplexCoefficient_hasFDerivAt realDeriv.differentiableAt).unique realDeriv)
  refine ⟨?_,point⟩
  change HasDerivAt G (scalarComplexCoefficient y z) z
  rw [coeff]
  exact derivG

/-- In the given original axes, without centering the horizontal line
in the hypotheses, both spatial reflections force zero peripheral
period for every Cartesian one-form on the conformal end. -/
theorem original_placed_axes_have_end_potentials {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ}
    (emb : IsClosedEmbedding X) (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (axes : OriginalHelicoidAxes (range X)) (approaches : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I axes.pitch 0)))
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    HasEndCartesianPotentials (X ∘ E.coord.symm) := by
  let c := axes.horizontalDirection
  let P := axes.horizontalPoint
  let C : Fin 3 → ℝ := ![0,0,P 2]
  let R := lineAxisCoordinates c axes.unit C
  obtain ⟨r,hr⟩ := original_axes_meet_before_compactification emb charts axes approaches
  have horizontal (s : ℝ) : (![s,0,0] : Fin 3 → ℝ)∈range (R ∘ X) := by
    obtain ⟨q,hq⟩ := axes.horizontal (r+s)
    have point : P+(r+s) • ![c.re,c.im,0]=C+s • ![c.re,c.im,0] := by rw [add_smul,← add_assoc,hr]
    exact ⟨q,(congrArg R (hq.trans point)).trans (lineAxisCoordinates_line c axes.unit C s)⟩
  have vertical (s : ℝ) : (![0,0,s] : Fin 3 → ℝ)∈range (R ∘ X) := by
    obtain ⟨q,hq⟩ := axes.vertical (s+P 2)
    refine ⟨q,(congrArg R hq).trans ?_⟩
    ext j
    fin_cases j <;> simp [R,lineAxisCoordinates,C,verticalRotation_apply]
  have chart (d : OpenPartialHomeomorph M ℂ) (hd : d∈atlas ℂ M) : HarmonicImmersionChart (R ∘ X) d := by
    intro z hz
    obtain ⟨h,k,i⟩ := charts d hd z hz
    exact lineAxisCoordinates_harmonic_chart c axes.unit C h k i
  have p : HasEndCartesianPotentials ((R ∘ X) ∘ E.coord.symm) :=
    two_axis_spatial_coordinates_have_end_primitives (R.isClosedEmbedding.comp emb) chart horizontal vertical E hol
  have eq : (fun z => verticalRotation c ((R ∘ X ∘ E.coord.symm) z)+C)=X ∘ E.coord.symm :=
    funext (fun z => R.symm_apply_apply (X (E.coord.symm z)))
  exact eq ▸ p.affine (verticalRotation c).toLinearMap C

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasEndCartesianPotentials.affine
#print axioms TwoAxisHelicoid.original_placed_axes_have_end_potentials
