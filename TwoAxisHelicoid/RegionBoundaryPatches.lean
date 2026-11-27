import TwoAxisHelicoid.ComplexBoundaryGraphIntegral
import TwoAxisHelicoid.RegionChartFormIntegrals

namespace TwoAxisHelicoid
open Complex Set Filter Topology MeasureTheory Function
open scoped Topology ContDiff Interval

/-- An oriented conformal boundary chart describes the physical region
as the upper side of a regular graph. Its middle curve lies in the chart. -/
structure CurveBoundaryGraph {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (Ω : Set M) where
  φ : ℝ → ℝ
  smooth : ContDiff ℝ 2 φ
  l : ℝ
  r : ℝ
  d : ℝ
  ordered : l≤r
  depth : 0<d
  side : ∀ q∈Icc (l,-d) (r,d),
    Complex.equivRealProdCLM.symm (realGraphShear φ q)∈curveChartRegion e Ω ↔ 0<q.2
  boundary : ∀ x∈Icc l r, Complex.equivRealProdCLM.symm (x,φ x)∈e.target

namespace CurveBoundaryGraph
variable {M : Type*} [TopologicalSpace M] {e : OpenPartialHomeomorph M ℂ} {Ω : Set M}

def box (G : CurveBoundaryGraph e Ω) : Set ℂ :=
  (Complex.equivRealProdCLM.symm ∘ realGraphShear G.φ) '' (Ioo G.l G.r ×ˢ Ioo (-G.d) G.d)

noncomputable def integral (G : CurveBoundaryGraph e Ω) (a : ℂ → ℂ) : ℝ :=
  ∫ x in G.l..G.r, ((⟨1,deriv G.φ x⟩:ℂ)*a (Complex.equivRealProdCLM.symm (x,G.φ x))).im

end CurveBoundaryGraph

/-- The two local alternatives required on the closure of an open
region. Every boundary patch carries its actual defining graph. -/
inductive CurveRegionPatch {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ) (Ω : Set M)
  | interior
  | boundary (graph : CurveBoundaryGraph e Ω)

namespace CurveRegionPatch
variable {M : Type*} [TopologicalSpace M] {e : OpenPartialHomeomorph M ℂ} {Ω : Set M}

/-- Physical supports for interior and boundary localizations. -/
def carrier : CurveRegionPatch e Ω → Set M
  | .interior => e.source ∩ Ω
  | .boundary G => e.source ∩ e ⁻¹' G.box

theorem carrier_subset_source (P : CurveRegionPatch e Ω) : P.carrier⊆e.source := by
  cases P <;> exact inter_subset_left

noncomputable def flux (P : CurveRegionPatch e Ω) (a : ℂ → ℂ) : ℝ :=
  match P with
  | .interior => 0
  | .boundary G => G.integral a

/-- On an interior patch Stokes gives zero. On a boundary patch the
integral is precisely the oriented graph integral, for the same cutoff
and the same physical region as in the surface partition. -/
theorem cutoff_flux (P : CurveRegionPatch e Ω) (op : IsOpen Ω) {ρ : M → ℝ}
    (compact : IsCompact (tsupport ρ)) (contained : tsupport ρ⊆P.carrier)
    {a : ℂ → ℂ} (sm : ∀ z∈e.target, ContDiffAt ℝ 1 (fun w => (ρ (e.symm w):ℂ)*a w) z) :
    (∫ z in curveChartRegion e Ω, complexFormExteriorCoefficient (fun w => (ρ (e.symm w):ℂ)*a w) z).im=
      P.flux (fun w => (ρ (e.symm w):ℂ)*a w) := by
  let f := fun w => (ρ (e.symm w):ℂ)*a w
  let K := e '' tsupport ρ
  have inside := contained.trans P.carrier_subset_source
  have ck : IsCompact K := compact.image_of_continuousOn (e.continuousOn.mono inside)
  have sub : K⊆e.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (inside hx)
  obtain ⟨g,sg,cs,sk,agree,off⟩ := extend_compact_chart_coefficient e.open_target ck sub sm (by
    intro z hz out
    have h : e.symm z∉tsupport ρ := fun mem => out ⟨_,mem,e.right_inv hz⟩
    rw [image_eq_zero_of_notMem_tsupport h,Complex.ofReal_zero,zero_mul])
  have replace : (∫ z in curveChartRegion e Ω, complexFormExteriorCoefficient f z)=
      ∫ z in curveChartRegion e Ω, complexFormExteriorCoefficient g z := by
    apply setIntegral_congr_fun (isOpen_curveChartRegion e op).measurableSet
    intro z hz
    exact congrArg (fun T : ℂ →L[ℝ] ℂ => I*T 1-T I) (agree z hz.1).fderiv_eq.symm
  change (∫ z in curveChartRegion e Ω, complexFormExteriorCoefficient f z).im=P.flux f
  cases P with
  | interior =>
    have inRegion : K⊆curveChartRegion e Ω := by
      rintro _ ⟨x,hx,rfl⟩
      have data : x∈e.source ∩ Ω := contained hx
      refine ⟨e.map_source data.1,?_⟩
      change e.symm (e x)∈Ω
      rw [e.left_inv data.1]
      exact data.2
    have all : (∫ z in curveChartRegion e Ω, complexFormExteriorCoefficient g z)=
        ∫ z, complexFormExteriorCoefficient g z := by
      symm
      rw [← setIntegral_univ]
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ _)
      intro z hz
      have eq := (off z (fun h => hz.2 (inRegion h))).fderiv_eq (𝕜:=ℝ)
      simp [complexFormExteriorCoefficient,eq]
    rw [replace,all,compact_complex_form_stokes sg cs]
    rfl
  | boundary G =>
    have inBox : tsupport g⊆G.box := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := sk hz
      exact (contained hx).2
    rw [replace,imaginary_form_integral_at_boundary_graph (isOpen_curveChartRegion e op)
      G.smooth G.ordered G.depth G.side sg cs inBox]
    apply intervalIntegral.integral_congr
    intro x hx
    have h := G.boundary x (by simpa only [uIcc_of_le G.ordered] using hx)
    exact congrArg (fun b : ℂ => ((⟨1,deriv G.φ x⟩:ℂ)*b).im) (agree _ h).self_of_nhds

end CurveRegionPatch
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CurveRegionPatch.cutoff_flux

