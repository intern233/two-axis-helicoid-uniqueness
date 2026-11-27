import TwoAxisHelicoid.TwoAxisPhysicalPoleExterior
import TwoAxisHelicoid.HorizontalLinePlacement
import TwoAxisHelicoid.GeometricHelicoidHypotheses

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology
open scoped Topology ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
  {X : M → Fin 3 → ℝ}

omit [IsManifold 𝓘(ℂ,ℂ) ω M] in
private theorem placement_harmonic_charts (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (c : ℂ) (hc : ‖c‖=1) (P : Fin 3 → ℝ) :
    ∀ d∈atlas ℂ M, HarmonicImmersionChart (lineAxisCoordinates c hc P ∘ X) d := by
  intro d hd z hz
  obtain ⟨h,k,i⟩ := charts d hd z hz
  exact lineAxisCoordinates_harmonic_chart c hc P h k i

/-- The original horizontal line intersects the original vertical axis,
even before constructing any conformal compactification or analytic
torus marking. Weak positional asymptotics suffice. -/
theorem original_axes_meet_before_compactification [PreconnectedSpace M] (emb : IsClosedEmbedding X)
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (axes : OriginalHelicoidAxes (range X))
    (approaches : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I axes.pitch 0))) :
    ∃ r : ℝ, axes.horizontalPoint+r • ![axes.horizontalDirection.re,axes.horizontalDirection.im,0]=
      ![0,0,axes.horizontalPoint 2] := by
  let c := axes.horizontalDirection
  let P := axes.horizontalPoint
  let R := lineAxisCoordinates c axes.unit P
  have line (s : ℝ) : (![s,0,0] : Fin 3 → ℝ)∈range (R ∘ X) := by
    obtain ⟨q,hq⟩ := axes.horizontal s
    exact ⟨q,(congrArg R hq).trans (lineAxisCoordinates_line c axes.unit P s)⟩
  obtain ⟨f,_,_,move⟩ := horizontal_schwarz_on_original_surface (R.isClosedEmbedding.comp emb)
    (placement_harmonic_charts charts c axes.unit P) line
  apply horizontal_half_turn_line_intersects_vertical_axis axes.pitch_ne approaches axes.vertical P
    ![c.re,c.im,0] rfl
  rintro _ ⟨q,rfl⟩
  exact ⟨f q,R.injective ((move q).trans (lineAxisCoordinates_half_turn c axes.unit P (X q)).symm)⟩

/-- Removing only a rotation about the vertical axis and a translation
from the spatial frame preserves the existence of a genuine exterior
height chart. The constant horizontal Gauss phase is integrated explicitly. -/
theorem exterior_in_original_horizontal_frame (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (c : ℂ) (hc : ‖c‖=1) (P : Fin 3 → ℝ) (G : GeometricExteriorCoordinate (lineAxisCoordinates c hc P ∘ X)) :
    ∃ B : GeometricExteriorCoordinate X, B.pitch=G.pitch := by
  let F := fun z : ℂ => G.correction z+log c
  have unit : c≠0 := fun eq => by simp [eq] at hc
  refine ⟨⟨G.chart,G.radius,G.positive,G.target,G.core,G.holomorphic,G.heightOffset+P 2,?_,
    G.pitch,G.pitch_ne,F,G.analytic.add analyticAt_const,?_⟩,rfl⟩
  · intro x hx
    have h := G.height x hx
    change X x 2-P 2=G.heightOffset+(G.chart x).re at h
    linarith
  · have chart := harmonic_immersion_chart_maximal charts G.holomorphic
    filter_upwards [G.gauss,tendsto_norm_cobounded_atTop.eventually_gt_atTop G.radius] with z formula large
    have hz : z∈G.chart.target := G.target ▸ large
    have der : DifferentiableAt ℝ (X ∘ G.chart.symm) z :=
      (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((chart z hz).1 j))).differentiableAt
    have mul := lineAxisCoordinates_gauss c hc P der
    change immersionGaussMap (lineAxisCoordinates c hc P ∘ (X ∘ G.chart.symm)) z=_ at formula
    rw [mul] at formula
    change immersionGaussMap (X ∘ G.chart.symm) z=exp (I*(G.pitch:ℂ)*z+(G.correction z⁻¹+log c))
    rw [← add_assoc,exp_add,exp_log unit,← formula]
    field_simp

/-- In the given physical axes, the original height and Gauss double
poles give a genuine exterior without a global uniformization, without
centering the horizontal line in the hypotheses, and for any genus. -/
theorem original_positional_poles_give_exterior [T2Space M] [PreconnectedSpace M] (emb : IsClosedEmbedding X)
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (axes : OriginalHelicoidAxes (range X))
    (approaches : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I axes.pitch 0)))
    (A : GeometricDoublePoleEnd X) : Nonempty (GeometricExteriorCoordinate X) := by
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
  have chart := harmonic_immersion_chart_maximal charts A.holomorphic
  have domain : A.endChart.coord.target∈𝓝[≠] (0:ℂ) := by
    rw [A.endChart.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ A.endChart.radius_pos)) self_mem_nhdsWithin
  have diff : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ (X ∘ A.endChart.coord.symm) z := by
    filter_upwards [domain] with z hz using
      (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((chart z hz).1 j))).differentiableAt
  have orders := lineAxisCoordinates_end_orders c axes.unit C diff
  have height := orders.1.trans A.heightOrder
  have gauss := orders.2.trans A.gaussOrder
  let B : GeometricDoublePoleEnd (R ∘ X) := ⟨A.endChart,A.holomorphic,
    meromorphicAt_of_meromorphicOrderAt_ne_zero (height.trans_ne (by norm_num)),height,
    meromorphicAt_of_meromorphicOrderAt_ne_zero (gauss.trans_ne (by norm_num)),gauss⟩
  obtain ⟨G,_,_⟩ := two_axis_double_poles_give_actual_exterior (R.isClosedEmbedding.comp emb)
    (placement_harmonic_charts charts c axes.unit C) horizontal vertical B
  obtain ⟨U,_⟩ := exterior_in_original_horizontal_frame charts c axes.unit C G
  exact ⟨U⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_axes_meet_before_compactification
#print axioms TwoAxisHelicoid.original_positional_poles_give_exterior
