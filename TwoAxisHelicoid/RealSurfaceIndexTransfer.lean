import TwoAxisHelicoid.SurfaceMorseIndex
import TwoAxisHelicoid.MinimalManifoldComplexStructure
import TwoAxisHelicoid.MaximalHarmonicImmersionChart
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Topology
open scoped Topology ContDiff Manifold BigOperators Matrix

/-- Compact negative variations in the initially given real smooth
structure. The support, the actual area Hessian, and smoothness of both
the scalar and ambient normal fields refer to that same immersion. -/
def HasInfiniteRealSurfaceMorseIndex {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) : Prop :=
  ∀ C : Set M, IsCompact C → ∀ n : ℕ, ∃ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (K : Set (ℝ × ℝ))
    (U : Fin n → M → ℝ) (N : M → Fin 3 → ℝ),
    let P := e.symm '' (translatedPlaneCoordinates c '' K)
    let ξ := fun z : ℂ => e.symm (z+c)
    let V := fun (i : Fin n) (x : M) => U i x • N x
    let variation := fun (a : Fin n → ℝ) (s : ℝ) (x : M) => X x+s • ((∑ i, a i*U i x) • N x)
    e ∈ IsManifold.maximalAtlas 𝓘(ℝ,ℂ) ∞ M ∧ IsCompact K ∧ (∀ p ∈ K, translatedPlaneCoordinates c p ∈ e.target) ∧ IsCompact P ∧ Disjoint P C ∧
    (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (U i) ∧ tsupport (U i) ⊆ P) ∧ LinearIndependent ℝ U ∧
    (∀ p ∈ K, (N (ξ (planeComplex p)) ⬝ᵥ N (ξ (planeComplex p))) = 1 ∧
      ∀ w : ℂ, N (ξ (planeComplex p)) ⬝ᵥ fderiv ℝ (X ∘ ξ) (planeComplex p) w = 0) ∧
    (∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (V i)) ∧ LinearIndependent ℝ V ∧
    (∀ a s x, x ∉ P → variation a s x = X x) ∧
    ∀ a : Fin n → ℝ, a ≠ 0 → deriv (deriv (fun s : ℝ => ∫ p in K,
      coordinateAreaDensity (variation a s ∘ ξ) (planeComplex p))) 0 < 0

/-- Every regular spatial chart is in the maximal real atlas of a
smooth immersed surface, including conformal charts introduced later. -/
theorem regular_spatial_chart_mem_real_maximal_atlas {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ,ℂ) ∞ M] {X : M → Fin 3 → ℝ}
    (old : ∀ p, RegularImmersionChart X (chartAt ℂ p)) {e : OpenPartialHomeomorph M ℂ}
    (regular : RegularImmersionChart X e) : e∈IsManifold.maximalAtlas 𝓘(ℝ,ℂ) ∞ M := by
  apply e.mem_maximalAtlas_of_contMDiffOn
  · intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    let d := chartAt ℂ x
    have dx : x∈d.source := mem_chart_source ℂ x
    have inside : d x∈(d.symm.trans e).source := ⟨d.map_source dx,by change d.symm (d x)∈e.source; rwa [d.left_inv dx]⟩
    have trans := regularImmersionChart_transition (old x) regular inside
    apply contMDiffAt_iff.mpr
    refine ⟨e.continuousAt hx,?_⟩
    simpa only [mfld_simps] using! trans.contDiffWithinAt (s := range 𝓘(ℝ,ℂ))
  · intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    let d := chartAt ℂ (e.symm z)
    have inside : z∈(e.symm.trans d).source := ⟨hz,mem_chart_source ℂ _⟩
    have trans := regularImmersionChart_transition regular (old _) inside
    apply contMDiffAt_iff.mpr
    refine ⟨e.symm.continuousAt hz,?_⟩
    simpa only [mfld_simps] using! trans.contDiffWithinAt (s := range 𝓘(ℝ,ℂ))

/-- Smoothness of arbitrary Euclidean-valued fields transfers between
two atlases parametrizing the same regular spatial immersion. -/
theorem smooth_in_original_regular_spatial_atlas {M E : Type*} [TopologicalSpace M] [orig : ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ,ℂ) ∞ M] [NormedAddCommGroup E] [NormedSpace ℝ E] {X : M → Fin 3 → ℝ}
    (old : ∀ p, RegularImmersionChart X (chartAt ℂ p)) (S : ChartedSpace ℂ M)
    (reg : ∀ p, RegularImmersionChart X (S.chartAt p)) (f : M → E)
    (smooth : let _ := S; ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,E) ∞ f) :
    (let _ := orig; ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,E) ∞ f) := by
  dsimp only
  let _ := orig
  intro x
  let e := S.chartAt x
  have ex : x∈e.source := S.mem_chart_source x
  have ef := regular_spatial_chart_mem_real_maximal_atlas old (reg x)
  have sf : ContDiffAt ℝ ∞ (f ∘ e.symm) (e x) := by
    let _ := S
    simpa only [mfld_simps,contDiffWithinAt_univ] using! (contMDiffAt_iff.mp (smooth x)).2
  have sm := (sf.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas ef ex))
  apply sm.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds ex] with p hp
  exact congrArg f (e.left_inv hp).symm

/-- A negative-variation space found in a compatible Riemann surface
atlas gives a space of equally many negative variations in the
original real smooth manifold. All spatial variations are identical. -/
theorem conformal_index_gives_original_real_index {M : Type*} [TopologicalSpace M] [orig : ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ,ℂ) ∞ M] {X : M → Fin 3 → ℝ} (old : ∀ p, RegularImmersionChart X (chartAt ℂ p))
    (S : ChartedSpace ℂ M) (man : let _ := S; IsManifold 𝓘(ℂ,ℂ) ω M)
    (charts : ∀ e∈S.atlas, HarmonicImmersionChart X e)
    (idx : let _ := S; HasInfiniteCompactSurfaceMorseIndex X) : (let _ := orig; HasInfiniteRealSurfaceMorseIndex X) := by
  dsimp only
  let _ := orig
  have reg (e : OpenPartialHomeomorph M ℂ) (he : HarmonicImmersionChart X e) : RegularImmersionChart X e := by
    intro z hz
    obtain ⟨harm,_,imm⟩ := he z hz
    exact ⟨(analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (harm j))).contDiffAt,imm⟩
  have smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : M → E) :=
    smooth_in_original_regular_spatial_atlas old S (fun p => reg _ (charts _ (S.chart_mem_atlas p))) f
  intro C kc n
  obtain ⟨e,c,K,U,N,hol,ck,inside,compact,disjoint,fields,ind,perp,vectors,vi,fixed,negative⟩ := idx C kc n
  have chart : HarmonicImmersionChart X e := by
    let _ := S
    let _ := man
    exact harmonic_immersion_chart_maximal charts hol
  refine ⟨e,c,K,U,N,regular_spatial_chart_mem_real_maximal_atlas old (reg _ chart),ck,inside,compact,disjoint,
    fun i => ⟨smooth _ (fields i).1,(fields i).2⟩,ind,perp,fun i => smooth _ (vectors i),vi,fixed,negative⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_spatial_chart_mem_real_maximal_atlas
#print axioms TwoAxisHelicoid.conformal_index_gives_original_real_index
