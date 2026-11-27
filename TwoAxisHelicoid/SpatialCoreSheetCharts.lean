import TwoAxisHelicoid.FiniteNormalGraphSheets
import TwoAxisHelicoid.CompactnessNormalCoreGraphs
import TwoAxisHelicoid.EmbeddedPitchGeometry

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology Manifold ContDiff

/-- Local sheets of a Euclidean normal tube, written in the given torus
marking. The patch may have multiple sheets and its projection need not be
known in advance to be proper or surjective. -/
structure SpatialCoreSheetCharts {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (W : PitchNormalizedBasicImmersion) where
  patch : Set (PeriodTorus (rhombicPeriodPair W.t W.ht))
  open_patch : IsOpen patch
  avoids : ∀ q : patch, q.1 ≠ 0
  base : EuclideanSpace ℝ (Fin 3) → C.carrier
  signedHeight : EuclideanSpace ℝ (Fin 3) → ℝ
  position : C.carrier → EuclideanSpace ℝ (Fin 3)
  normal : C.carrier → EuclideanSpace ℝ (Fin 3)
  baseContinuous : ContinuousOn base (W.torusPosition '' patch)
  heightContinuous : ContinuousOn signedHeight (W.torusPosition '' patch)
  graph : ∀ q : patch, W.torusPosition q.1 = position (base (W.torusPosition q.1))+
    signedHeight (W.torusPosition q.1) • normal (base (W.torusPosition q.1))
  charts : ∀ b : C.carrier, FiniteSheetGerms (fun q : patch => base (W.torusPosition q.1)) b
  smoothSheets : ∀ (b : C.carrier) (i : Fin ((charts b).extraSheets+1)),
    ∃ f : PeriodTorus A → PeriodTorus (rhombicPeriodPair W.t W.ht),
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) 1 f b.1 ∧ ∀ᶠ v in 𝓝 b, f v.1 = ((charts b).sheet i v).1

theorem embedded_pitch_spatial_marking_closed (W : PitchNormalizedBasicImmersion) (hW : W ∈ embeddedPitchFamily) :
    IsClosedEmbedding (fun q : PuncturedPeriodTorus (rhombicPeriodPair W.t W.ht) => W.torusPosition q.1) := by
  obtain ⟨h,_,_,he,_,_,_,_⟩ := embedded_pitch_family_unit_helicoid_geometry W hW
  let L := rhombicPeriodPair W.t W.ht
  have eq : (fun q : PuncturedPeriodTorus L => W.torusPosition q.1) = coordinateToEuclidean ∘ harmonicTorusImmersion h := by
    funext q
    obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L q
    change W.torusPosition (periodTorusProjection L z.1) = coordinateToEuclidean (harmonicTorusImmersion h _)
    rw [W.torusPosition_projection z.1 z.2]
    exact congrArg coordinateToEuclidean (harmonicTorusImmersion_projection h z.2).symm
  rw [eq]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp he

/-- Exhaustion by disjoint local graphs in the signed normal coordinate
gives all projection properties used in the genus and flux argument. -/
noncomputable def SpatialCoreSheetCharts.toNormalCorePatch {A : PeriodPair} {C : TorusGeneratingCoreModel A}
    {W : PitchNormalizedBasicImmersion} (G : SpatialCoreSheetCharts C W) (hW : W ∈ embeddedPitchFamily) :
    TorusNormalCorePatch C (rhombicPeriodPair W.t W.ht) := by
  let L := rhombicPeriodPair W.t W.ht
  let j := fun q : G.patch => (⟨q.1,G.avoids q⟩ : PuncturedPeriodTorus L)
  let Y := fun q : G.patch => W.torusPosition q.1
  let π := G.base ∘ Y
  let u := G.signedHeight ∘ Y
  have hY := embedded_pitch_spatial_marking_closed W hW
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hc : Continuous Y := hY.continuous.comp hj
  have hy (q : G.patch) : Y q ∈ W.torusPosition '' G.patch := ⟨_,q.2,rfl⟩
  have hπ : Continuous π := G.baseContinuous.comp_continuous hc hy
  have hu : Continuous u := G.heightContinuous.comp_continuous hc hy
  have props := proper_projection_of_finite_sheet_germs hπ G.charts
  refine ⟨G.patch,G.open_patch,G.avoids,π,props.1,props.2.1,props.2.2,u,hu,?_,?_⟩
  · intro x y hbase hheight
    change G.base (Y x) = G.base (Y y) at hbase
    change G.signedHeight (Y x) = G.signedHeight (Y y) at hheight
    have eq : Y x = Y y := (G.graph x).trans (by
      change G.position (G.base (Y x))+G.signedHeight (Y x) • G.normal (G.base (Y x)) = Y y
      rw [hbase,hheight]
      exact (G.graph y).symm)
    have e : j x = j y := hY.injective eq
    exact Subtype.ext (congrArg (fun w : PuncturedPeriodTorus L => w.1) e)
  · intro q
    obtain ⟨i,hi⟩ := (G.charts (π q)).exists_sheet (x := q) rfl
    obtain ⟨f,hf,he⟩ := G.smoothSheets (π q) i
    refine ⟨f,hf,?_⟩
    filter_upwards [hπ.continuousAt he,(G.charts (π q)).inverseGerm hπ rfl hi] with b hb hinv
    exact hb.trans (congrArg Subtype.val hinv)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.SpatialCoreSheetCharts.toNormalCorePatch
