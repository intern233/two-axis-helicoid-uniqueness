import TwoAxisHelicoid.SpatialCoreSheetCharts
import TwoAxisHelicoid.SmoothImmersionLeftInverse
import TwoAxisHelicoid.PointedTorusUniformization

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology Manifold ContDiff

/-- A local smooth inverse to the actual Euclidean position on the surface.
The inverse is defined on ambient three-space and its values lie in the
original marked torus. -/
theorem embedded_pitch_ambient_inverse_germ (W : PitchNormalizedBasicImmersion) (hW : W ∈ embeddedPitchFamily)
    (q : PuncturedPeriodTorus (rhombicPeriodPair W.t W.ht)) :
    let L := rhombicPeriodPair W.t W.ht
    ∃ G : EuclideanSpace ℝ (Fin 3) → PeriodTorus L,
      ContMDiffAt 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ,ℂ) 1 G (W.torusPosition q.1) ∧
      ∀ᶠ y : PuncturedPeriodTorus L in 𝓝 q, G (W.torusPosition y.1) = y.1 := by
  let L := rhombicPeriodPair W.t W.ht
  let e := chartAt ℂ q.1
  let z := e q.1
  have hq : q.1 ∈ e.source := mem_chart_source _ _
  have hp (u : PeriodTorus L) (hu : u ∈ e.source) : periodTorusProjection L (e u) = u := by
    rw [← periodTorus_chart_symm_eq_projection L q.1]
    exact e.left_inv hu
  have hreg (y : PuncturedPeriodTorus L) (hy : y.1 ∈ e.source) : e y.1 ∉ L.lattice :=
    fun hn => y.2 ((hp _ hy).symm.trans ((periodTorusProjection_eq_zero L _).mpr hn))
  have hcoord (y : PuncturedPeriodTorus L) (hy : y.1 ∈ e.source) :
      W.torusPosition y.1 = coordinateToEuclidean (W.position (e y.1)) :=
    (congrArg W.torusPosition (hp _ hy).symm).trans (W.torusPosition_projection _ (hreg y hy))
  obtain ⟨h,_⟩ := hW
  have hX : AnalyticAt ℝ W.position z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (h.harmonic z (hreg q hq) j)
  obtain ⟨g,U,hU,hz,hg,hinv⟩ := smooth_local_left_inverse (hX.contDiffAt (n := ∞)) (h.immersion z (hreg q hq))
  let A := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let f := fun v : EuclideanSpace ℝ (Fin 3) => g (A v)
  have hgA : ContDiffAt ℝ 1 g (A (W.torusPosition q.1)) := by
    rw [hcoord q hq]
    exact hg.of_le (by simp)
  have hf : ContDiffAt ℝ 1 f (W.torusPosition q.1) :=
    hgA.comp (W.torusPosition q.1) (A.contDiff.contDiffAt : ContDiffAt ℝ 1 (fun v => A v) _)
  have hπ : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) 1 (periodTorusProjection L) := by
    intro w
    obtain ⟨a,ha,he⟩ := periodTorusProjection_isLocalHomeomorph L w
    have hmem : a.symm ∈ atlas ℂ (PeriodTorus L) := he.symm
    have hc := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,ℂ)) (n := ω) (IsManifold.subset_maximalAtlas hmem) ha
    rw [he]
    exact hc.of_le (by simp)
  refine ⟨periodTorusProjection L ∘ f,hπ.contMDiffAt.comp _ (contMDiffAt_iff_contDiffAt.mpr hf),?_⟩
  have hcont : ContinuousAt (fun y : PuncturedPeriodTorus L => e y.1) q := (e.continuousAt hq).comp continuous_subtype_val.continuousAt
  filter_upwards [hcont (hU.mem_nhds hz),continuous_subtype_val.continuousAt (e.open_source.mem_nhds hq)] with y hy hs
  change periodTorusProjection L (g (A (W.torusPosition y.1))) = y.1
  rw [hcoord y hs]
  exact (congrArg (periodTorusProjection L) (hinv _ hy)).trans (hp _ hs)

/-- The smooth torus inverse germs required by the compact-core argument
follow from smooth Euclidean sheets and continuity in the subspace topology.
The hypothesis only refers to the spatial position of the sheet. -/
theorem torus_sheet_inverse_germ_of_spatial_section {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (W : PitchNormalizedBasicImmersion) (hW : W ∈ embeddedPitchFamily) (b : C.carrier)
    (σ : C.carrier → PuncturedPeriodTorus (rhombicPeriodPair W.t W.ht)) (hσ : ContinuousAt σ b)
    (S : PeriodTorus A → EuclideanSpace ℝ (Fin 3)) (hS : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) 1 S b.1)
    (hpos : ∀ᶠ v in 𝓝 b, S v.1 = W.torusPosition (σ v).1) :
    ∃ f : PeriodTorus A → PeriodTorus (rhombicPeriodPair W.t W.ht), ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) 1 f b.1 ∧
      ∀ᶠ v in 𝓝 b, f v.1 = (σ v).1 := by
  obtain ⟨G,hG,hinv⟩ := embedded_pitch_ambient_inverse_germ W hW (σ b)
  have h₀ := hpos.self_of_nhds
  rw [← h₀] at hG
  refine ⟨G ∘ S,hG.comp _ hS,?_⟩
  filter_upwards [hpos,hσ hinv] with v hv hi
  exact (congrArg G hv).trans hi

/-- Transport an exhaustive finite local family through a homeomorphic
change of the total space, without choosing orders on its sheets. -/
noncomputable def FiniteSheetGerms.pullback {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (e : E ≃ₜ F) {p : E → B} {r : F → B} (hp : ∀ x, p x = r (e x)) {b : B} (G : FiniteSheetGerms r b) :
    FiniteSheetGerms p b where
  extraSheets := G.extraSheets
  sheet := fun i v => e.symm (G.sheet i v)
  continuousAt := fun i => e.symm.continuous.continuousAt.comp (G.continuousAt i)
  distinct := fun _ _ eq => G.distinct (e.symm.injective eq)
  fiber := by
    filter_upwards [G.fiber] with v hv
    ext x
    change p x = v ↔ ∃ i, e.symm (G.sheet i v) = x
    constructor
    · intro h
      have hm : e x ∈ range (fun i => G.sheet i v) := hv ▸ (show e x ∈ r ⁻¹' {v} from (hp x).symm.trans h)
      obtain ⟨i,hi⟩ := hm
      exact ⟨i,(congrArg e.symm hi).trans (e.symm_apply_apply x)⟩
    · rintro ⟨i,rfl⟩
      rw [hp,e.apply_symm_apply]
      exact (show G.sheet i v ∈ r ⁻¹' {v} from hv ▸ mem_range_self i)

/-- Actual Euclidean sheets over the core give the torus chart hypotheses.
All smooth extensions in the input take values in ambient three-space. -/
noncomputable def spatial_core_charts_of_ambient_sheets {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (W : PitchNormalizedBasicImmersion) (hW : W ∈ embeddedPitchFamily)
    (P : Set (PeriodTorus (rhombicPeriodPair W.t W.ht))) (hP : IsOpen P) (avoid : ∀ q : P, q.1 ≠ 0)
    (base : EuclideanSpace ℝ (Fin 3) → C.carrier) (height : EuclideanSpace ℝ (Fin 3) → ℝ)
    (X N : C.carrier → EuclideanSpace ℝ (Fin 3)) (hb : ContinuousOn base (W.torusPosition '' P))
    (hh : ContinuousOn height (W.torusPosition '' P))
    (graph : ∀ y ∈ W.torusPosition '' P, y = X (base y)+height y • N (base y))
    (D : ∀ b : C.carrier, FiniteSheetGerms (fun y : W.torusPosition '' P => base y.1) b)
    (smooth : ∀ (b : C.carrier) (i : Fin ((D b).extraSheets+1)),
      ∃ S : PeriodTorus A → EuclideanSpace ℝ (Fin 3), ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) 1 S b.1 ∧
        ∀ᶠ v in 𝓝 b, S v.1 = ((D b).sheet i v).1) : SpatialCoreSheetCharts C W := by
  let L := rhombicPeriodPair W.t W.ht
  have sub : P ⊆ {q : PeriodTorus L | q ≠ 0} := fun q h => avoid ⟨q,h⟩
  let y := fun a : P => W.torusPosition a.1
  have inc : IsEmbedding y := (embedded_pitch_spatial_marking_closed W hW).isEmbedding.comp (IsEmbedding.inclusion sub)
  have eq : range y = W.torusPosition '' P := by
    ext v
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨_,q.2,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq⟩,rfl⟩
  let e := inc.toHomeomorph.trans (Homeomorph.setCongr eq)
  have he (q : P) : (e q).1 = y q := rfl
  let G := fun b : C.carrier => (D b).pullback e (p := fun q : P => base (y q)) (fun _ => rfl)
  refine ⟨P,hP,avoid,base,height,X,N,hb,hh,fun q => graph _ ⟨_,q.2,rfl⟩,G,?_⟩
  intro b i
  obtain ⟨S,hS,hpos⟩ := smooth b i
  let σ := fun v => (Set.inclusion sub ((G b).sheet i v) : PuncturedPeriodTorus L)
  have hc : ContinuousAt σ b := (IsEmbedding.inclusion sub).continuous.continuousAt.comp ((G b).continuousAt i)
  apply torus_sheet_inverse_germ_of_spatial_section C W hW b σ hc S hS
  filter_upwards [hpos] with v hv
  apply hv.trans
  change ((D b).sheet i v).1 = y (e.symm ((D b).sheet i v))
  exact (congrArg Subtype.val (e.apply_symm_apply ((D b).sheet i v))).symm.trans (he _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_sheet_inverse_germ_of_spatial_section
#print axioms TwoAxisHelicoid.spatial_core_charts_of_ambient_sheets
