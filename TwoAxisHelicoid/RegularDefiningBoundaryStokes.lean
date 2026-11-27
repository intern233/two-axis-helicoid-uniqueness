import TwoAxisHelicoid.RegularBoundaryGraphFunction
import TwoAxisHelicoid.SmoothBoundaryGraphGerms
import TwoAxisHelicoid.SmoothRegionGreenIdentities

namespace TwoAxisHelicoid
open Complex Set Topology Function Filter
open scoped Topology ContDiff Manifold

/-- An ordinary regular C² defining function near every physical
boundary point of a Riemann surface. Its gradient can have any
nonzero direction in the supplied chart. -/
def HasRegularDefiningBoundary {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (Ω : Set M) : Prop :=
  ∀ p∈frontier Ω, ∃ e : OpenPartialHomeomorph M ℂ, e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ p∈e.source ∧
    ∃ F : ℂ → ℝ, ContDiffAt ℝ 2 F (e p) ∧ F (e p)=0 ∧ fderiv ℝ F (e p)≠0 ∧
      ∀ᶠ z in 𝓝 (e p), z∈curveChartRegion e Ω ↔ 0<F z

/-- Rotate and rescale the conformal coordinate so that the vertical
derivative of the defining function is positive. The implicit
function theorem then supplies the actual boundary graph. -/
theorem regular_defining_boundary_has_graph_germs {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {Ω : Set M} (boundary : HasRegularDefiningBoundary Ω) :
    HasSmoothBoundaryGraphGerms Ω := by
  intro p hp
  obtain ⟨e,he,hp,F,sm,zero,nz,side⟩ := boundary p hp
  let A := fderiv ℝ F (e p)
  obtain ⟨v,positive⟩ : ∃ v : ℂ, 0<A v := by
    by_contra! nonpos
    apply nz
    apply ContinuousLinearMap.ext
    intro w
    change A w=0
    exact le_antisymm (nonpos w) (by simpa only [map_neg,neg_nonpos] using nonpos (-w))
  have vn : v≠0 := fun h => by simp only [h,map_zero,lt_self_iff_false] at positive
  let L := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (v/I) (div_ne_zero vn I_ne_zero))
  let d := e.trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  have mem : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
    apply d.mem_maximalAtlas_of_contMDiffOn
    · intro x hx
      exact ((contMDiffAt_iff_contDiffAt.mpr (L.symm.contDiff.contDiffAt (x:=e x))).comp x
        (contMDiffAt_of_mem_maximalAtlas he hx.1)).contMDiffWithinAt
    · intro z hz
      exact ((contMDiffAt_symm_of_mem_maximalAtlas he hz.2).comp z
        (contMDiffAt_iff_contDiffAt.mpr L.contDiff.contDiffAt)).contMDiffWithinAt
  have dp : p∈d.source := ⟨hp,mem_univ _⟩
  let E := Complex.equivRealProdCLM.symm
  let T := (L.toContinuousLinearMap.restrictScalars ℝ).comp E.toContinuousLinearMap
  let q := Complex.equivRealProdCLM (d p)
  have tq : T q=e p := by
    change L (E (E.symm (L.symm (e p))))=e p
    rw [E.apply_symm_apply,L.apply_symm_apply]
  have tv : T (0,1)=v := by
    change (⟨0,1⟩:ℂ)*(v/I)=v
    change I*(v/I)=v
    field_simp
  have dF : HasFDerivAt (F ∘ T) (A.comp T) q := (show HasFDerivAt F A (T q) by
    rw [tq]; exact (sm.differentiableAt (by norm_num)).hasFDerivAt).comp q T.hasFDerivAt
  have sF : ContDiffAt ℝ 2 (F ∘ T) q := (show ContDiffAt ℝ 2 F (T q) by rwa [tq]).comp q T.contDiff.contDiffAt
  obtain ⟨φ,cφ,center,graph⟩ := regular_defining_function_upper_graph sF (by simp only [Function.comp_apply,tq,zero])
    (by rw [dF.fderiv,ContinuousLinearMap.comp_apply,tv]; exact positive)
  refine ⟨d,mem,dp,φ,cφ,center.symm,?_⟩
  have original : Tendsto L (𝓝 (d p)) (𝓝 (e p)) := by
    have eq : L (d p)=e p := L.apply_symm_apply _
    exact eq ▸ L.continuous.continuousAt
  filter_upwards [original.eventually side,(Complex.equivRealProdCLM.continuous.continuousAt (x:=d p)).eventually graph] with z hz gz
  have prev : z∈curveChartRegion d Ω ↔ L z∈curveChartRegion e Ω := by
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨mem_univ _,h.1⟩,h.2⟩⟩
  have identify : T (Complex.equivRealProdCLM z)=L z := congrArg L (E.apply_symm_apply z)
  change 0<F (T (Complex.equivRealProdCLM z)) ↔ φ z.re<z.im at gz
  rw [identify] at gz
  exact prev.trans (hz.trans gz)

/-- Appendix D.4 for any open relatively compact region with a
regular defining boundary on the given minimal surface. The only PDE
hypotheses are the two classical Jacobi equations. -/
theorem jacobi_green_on_regular_defining_regions {M : Type*} [TopologicalSpace M] [T2Space M]
    [SigmaCompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {Ω : Set M} (op : IsOpen Ω) (compact : IsCompact (closure Ω)) (boundary : HasRegularDefiningBoundary Ω)
    (X : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (u v : M → ℝ) (su : IsSurfaceJacobiField X u) (sv : IsSurfaceJacobiField X v) :
    Nonempty (CurveRegionPartition Ω) ∧ ∀ P : CurveRegionPartition Ω,
      P.jacobiBoundaryFlux u v X-P.jacobiBoundaryFlux v u X=0 ∧ P.jacobiEnergy X u=P.jacobiBoundaryFlux u u X :=
  smooth_region_jacobi_green_identities op compact (smooth_curve_boundary_of_graph_germs
    (regular_defining_boundary_has_graph_germs boundary)) X hX u v su sv

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_defining_boundary_has_graph_germs
#print axioms TwoAxisHelicoid.jacobi_green_on_regular_defining_regions

