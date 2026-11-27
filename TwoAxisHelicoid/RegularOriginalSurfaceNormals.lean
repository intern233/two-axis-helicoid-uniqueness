import TwoAxisHelicoid.OrientedHarmonicNormal
import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.OriginalHelicoidMetric
import TwoAxisHelicoid.RegularChartNormalStability
import TwoAxisHelicoid.CompactCoreUnorientedNormalLimit

namespace TwoAxisHelicoid
open Complex Set Metric Filter Matrix Topology
open scoped Topology ContDiff Manifold RealInnerProductSpace

private theorem core_tube_cartesian_inner (a b : Fin 3 → ℝ) :
    ⟪coordinateToEuclidean a,coordinateToEuclidean b⟫=a ⬝ᵥ b := by
  rw [coordinateToEuclidean_apply,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_comm]

/-- The unit normal bundle as a subset of physical position--direction
space, computed in the original real smooth immersion charts. -/
def OriginalSmoothHelicoid.unorientedNormals (s : OriginalSmoothHelicoid) :
    Set (SurfaceEuclideanSpace × SurfaceEuclideanSpace) :=
  {q | ∃ b, s.euclideanPosition b=q.1 ∧ ‖q.2‖=1 ∧ ∀ u∈chartEuclideanTangent s.position
    (chartAt ℂ b) ((chartAt ℂ b) b), ⟪u,q.2⟫=0}

/-- A single continuous normal field on the whole original surface has
regular local coordinates for the normal tube. Its two signs recover
precisely the geometric unit-normal bundle in the original real charts. -/
theorem original_smooth_regular_normal_geometry (s : OriginalSmoothHelicoid) :
    ∃ N : s.carrier → SurfaceEuclideanSpace, Continuous N ∧ (∀ p, ‖N p‖=1) ∧
      s.unorientedNormals=unorientedSurfaceNormals s.euclideanPosition N ∧
      ∃ S : ChartedSpace ℂ s.carrier, ∀ p, let e := S.chartAt p; let z := e p
        ContDiffAt ℝ 1 (s.euclideanPosition ∘ e.symm) z ∧ ContDiffAt ℝ 1 (N ∘ e.symm) z ∧
        Function.Injective (fderiv ℝ (s.euclideanPosition ∘ e.symm) z) ∧ ‖N p‖=1 ∧
        ∀ v, ⟪fderiv ℝ (s.euclideanPosition ∘ e.symm) z v,N p⟫=0 := by
  let d := fun p : s.carrier => chartAt ℂ p
  have ds (p : s.carrier) : p∈(d p).source := mem_chart_source ℂ p
  have dr := smooth_surface_regular_manifold_chart s.smooth s.immersion
  obtain ⟨V,_,S,man,charts⟩ := punctured_torus_minimal_induced_oriented_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  let _ := man
  obtain ⟨n,form,unit,ct⟩ := oriented_harmonic_atlas_unit_normal charts
  let N := coordinateToEuclidean ∘ n
  have un (p : s.carrier) : ‖N p‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← real_inner_self_eq_norm_sq,show ⟪N p,N p⟫=n p ⬝ᵥ n p from core_tube_cartesian_inner _ _,unit,one_pow]
  have data (p : s.carrier) : let e := S.chartAt p; let z := e p
      ContDiffAt ℝ 1 (s.euclideanPosition ∘ e.symm) z ∧ ContDiffAt ℝ 1 (N ∘ e.symm) z ∧
      Function.Injective (fderiv ℝ (s.euclideanPosition ∘ e.symm) z) ∧ ‖N p‖=1 ∧
      ∀ v, ⟪fderiv ℝ (s.euclideanPosition ∘ e.symm) z v,N p⟫=0 := by
    let e := S.chartAt p
    let x := e p
    let Y := s.position ∘ e.symm
    have ep : p∈e.source := S.mem_chart_source p
    have ez : x∈e.target := e.map_source ep
    have he : e∈S.atlas := S.chart_mem_atlas p
    obtain ⟨h,c,i⟩ := (charts e he).2 x ez
    have an : AnalyticAt ℝ Y x := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (h j)
    have data := harmonicChartNormal_data an c i
    have nh : n ∘ e.symm=ᶠ[𝓝 x] harmonicChartNormal Y := Filter.mem_of_superset (e.open_target.mem_nhds ez) (fun z h => form e he z h)
    have np : n p=harmonicChartNormal Y x := by simpa only [Function.comp_apply,x,e.left_inv ep] using nh.self_of_nhds
    have d := coordinateToEuclidean.hasFDerivAt.comp x an.differentiableAt.hasFDerivAt
    have nf : AnalyticAt ℝ (n ∘ e.symm) x := data.1.congr nh.symm
    refine ⟨(coordinateToEuclidean.analyticAt _ |>.comp an).contDiffAt,(coordinateToEuclidean.analyticAt _ |>.comp nf).contDiffAt,?_,un p,?_⟩
    · change Function.Injective (fderiv ℝ (coordinateToEuclidean ∘ Y) x)
      rw [d.fderiv]
      exact surfaceCartesianEquiv.symm.injective.comp i
    · intro v
      change ⟪fderiv ℝ (coordinateToEuclidean ∘ Y) x v,coordinateToEuclidean (n p)⟫=0
      rw [d.fderiv,ContinuousLinearMap.comp_apply,core_tube_cartesian_inner,np,dotProduct_comm,real_linear_complex_expansion (fderiv ℝ Y x) v]
      simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]
      have a := data.2.2.2.2.2.2.1
      have b := data.2.2.2.2.2.2.2
      change harmonicChartNormal Y x ⬝ᵥ fderiv ℝ Y x 1=0 at a
      change harmonicChartNormal Y x ⬝ᵥ fderiv ℝ Y x I=0 at b
      rw [a,b,mul_zero,mul_zero,add_zero]
  refine ⟨N,coordinateToEuclidean.continuous.comp ct,un,?_,S,data⟩
  have plane (p : s.carrier) : chartEuclideanTangent s.position (d p) ((d p) p)=
      (fderiv ℝ (s.euclideanPosition ∘ (S.chartAt p).symm) ((S.chartAt p) p)).toLinearMap.range := by
    let e := S.chartAt p
    have he := charts e (S.chart_mem_atlas p)
    have regular := he.1.1 (e p) (e.map_source (S.mem_chart_source p))
    have derivEq := coordinateToEuclidean.hasFDerivAt.comp (e p) (regular.1.differentiableAt (by simp)).hasFDerivAt
    calc
      _=chartEuclideanTangent s.position e (e p) := chartEuclideanTangent_eq (dr p) he.1.1 (ds p) (S.mem_chart_source p)
      _=_ := by
        change _=(fderiv ℝ (coordinateToEuclidean ∘ (s.position ∘ e.symm)) (e p)).toLinearMap.range
        rw [derivEq.fderiv]
        rfl
  ext q
  constructor
  · rintro ⟨p,pos,uq,perp⟩
    have ort : ∀ v, ⟪fderiv ℝ (s.euclideanPosition ∘ (S.chartAt p).symm) ((S.chartAt p) p) v,q.2⟫=0 :=
      fun v => perp _ ((plane p).symm ▸ (show _∈(fderiv ℝ (s.euclideanPosition ∘ (S.chartAt p).symm) ((S.chartAt p) p)).toLinearMap.range from ⟨v,rfl⟩))
    exact ⟨p,pos,regular_plane_unit_normal_choices (data p).2.2.1 (un p) uq (data p).2.2.2.2 ort⟩
  · rintro ⟨p,pos,sign⟩
    refine ⟨p,pos,?_,?_⟩
    · rcases sign with h|h
      · rw [h,un]
      · rw [h,norm_neg,un]
    · intro u hu
      have inRange := (plane p) ▸ hu
      obtain ⟨v,ev⟩ := inRange
      change fderiv ℝ (s.euclideanPosition ∘ (S.chartAt p).symm) ((S.chartAt p) p) v=u at ev
      rw [← ev]
      rcases sign with h|h
      · rw [h,(data p).2.2.2.2]
      · rw [h,inner_neg_right,(data p).2.2.2.2,neg_zero]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_smooth_regular_normal_geometry
