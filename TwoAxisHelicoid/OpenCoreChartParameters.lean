import TwoAxisHelicoid.PhysicalCoreGraphChartConvergence
import TwoAxisHelicoid.OriginalRegularChartNormals

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- Read a regular reference chart in an open core; values outside
the core are immaterial to all of the derivative germs. -/
noncomputable def coreChartParameter {B : Type*} [TopologicalSpace B] (V : Set B) (b : V)
    (a : OpenPartialHomeomorph B ℂ) (z : ℂ) : V := by
  classical
  exact if h : a.symm z∈V then ⟨a.symm z,h⟩ else b

def coreChartRegion {B : Type*} [TopologicalSpace B] (V : Set B) (a : OpenPartialHomeomorph B ℂ) : Set ℂ :=
  a.target ∩ a.symm ⁻¹' V

theorem coreChartRegion_open {B : Type*} [TopologicalSpace B] {V : Set B} (vo : IsOpen V)
    (a : OpenPartialHomeomorph B ℂ) : IsOpen (coreChartRegion V a) :=
  a.symm.continuousOn.isOpen_inter_preimage a.open_target vo

theorem coreChartParameter_val {B : Type*} [TopologicalSpace B] {V : Set B} (b : V) (a : OpenPartialHomeomorph B ℂ)
    {z : ℂ} (hz : z∈coreChartRegion V a) : (coreChartParameter V b a z).1=a.symm z := by
  classical
  have h : a.symm z∈V := hz.2
  simp only [coreChartParameter,dite_eq_left h]

theorem coreChartParameter_continuousOn {B : Type*} [TopologicalSpace B] {V : Set B} (b : V)
    (a : OpenPartialHomeomorph B ℂ) : ContinuousOn (coreChartParameter V b a) (coreChartRegion V a) := by
  apply IsInducing.subtypeVal.continuousOn_iff.mpr
  apply (a.symm.continuousOn.mono (inter_subset_left)).congr
  intro z hz
  exact coreChartParameter_val b a hz

/-- The converging spatial maps are the actual moving points read in
every regular parametrization of the original limit surface. Both
the height derivative and the spatial derivative use that same chart. -/
theorem physical_graph_C1_on_original_surface (s : OriginalSmoothHelicoid) {V : Set s.carrier}
    (vo : IsOpen V) (b : V) {N : s.carrier → SurfaceEuclideanSpace} (cn : Continuous N) (unitN : ∀ p, ‖N p‖=1)
    (normals : s.unorientedNormals=unorientedSurfaceNormals s.euclideanPosition N)
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] {Y m : ∀ k, M k → SurfaceEuclideanSpace} {r : ℝ}
    (G : ∀ k, PhysicalCoreGraph (fun q : V × ℝ => s.euclideanPosition q.1.1+q.2 • N q.1.1) (Y k) r)
    (moving : ∀ k y, ∃ a : OpenPartialHomeomorph (M k) ℂ, y∈a.source ∧
      ContDiffAt ℝ 1 (Y k ∘ a.symm) (a y) ∧ Function.Injective (fderiv ℝ (Y k ∘ a.symm) (a y)) ∧
      ∀ v, ⟪fderiv ℝ (Y k ∘ a.symm) (a y) v,m k y⟫=0)
    (unit : ∀ k y, ‖m k y‖=1) (near : ∀ k q, coreNormalDistance (m k ((G k).point q)) (N q.1)<1)
    (limit : ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop, ∀ q, |(G k).height q|<ε ∧ coreNormalDistance (m k ((G k).point q)) (N q.1)<ε)
    (a : OpenPartialHomeomorph s.carrier ℂ) (regular : RegularImmersionChart s.position a) :
    let U := coreChartRegion V a
    let p := coreChartParameter V b a
    let u := fun k => (G k).height ∘ p
    let Z := fun k => Y k ∘ (G k).point ∘ p
    (∀ k z, z∈U → ContDiffAt ℝ 1 (u k) z ∧ ContDiffAt ℝ 1 (Z k) z) ∧
      TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) (fun _ => 0) atTop U ∧
      TendstoLocallyUniformlyOn (fun k => fderiv ℝ (Z k)) (fderiv ℝ (s.euclideanPosition ∘ a.symm)) atTop U := by
  intro U p u Z
  let X := fun q : V => s.euclideanPosition q.1
  let n := fun q : V => N q.1
  have op := coreChartRegion_open vo a
  have germ (z : ℂ) (hz : z∈U) : ((Subtype.val : V → s.carrier) ∘ p)=ᶠ[𝓝 z] a.symm :=
    Filter.mem_of_superset (op.mem_nhds hz) (fun w hw => coreChartParameter_val b a hw)
  have pos (z : ℂ) (hz : z∈U) : X ∘ p=ᶠ[𝓝 z] s.euclideanPosition ∘ a.symm := (germ z hz).fun_comp s.euclideanPosition
  have nor (z : ℂ) (hz : z∈U) : n ∘ p=ᶠ[𝓝 z] N ∘ a.symm := (germ z hz).fun_comp N
  have data (z : ℂ) (hz : z∈U) := original_unit_normal_in_arbitrary_regular_chart s cn unitN normals a regular hz.1
  have orth (z : ℂ) (hz : z∈U) : ‖n (p z)‖=1 ∧ ∀ v, ⟪fderiv ℝ (X ∘ p) z v,n (p z)⟫=0 := by
    refine ⟨unitN _,?_⟩
    intro v
    rw [(pos z hz).fderiv_eq,show n (p z)=N (a.symm z) from (nor z hz).self_of_nhds]
    exact (data z hz).2.2.2 v
  obtain ⟨sm,dh,sp⟩ := physical_core_graphs_C1_in_parameter (X := X) (N := n) G moving unit near limit op p
    (coreChartParameter_continuousOn b a) (fun z hz => (data z hz).1.congr_of_eventuallyEq (pos z hz))
    (fun z hz => (data z hz).2.1.congr_of_eventuallyEq (nor z hz)) orth
  exact ⟨sm,dh,sp.congr_right (fun z hz => (pos z hz).fderiv_eq)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_graph_C1_on_original_surface
