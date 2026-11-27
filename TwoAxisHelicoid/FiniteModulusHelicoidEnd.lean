import TwoAxisHelicoid.AnnulusBoundarySector
import TwoAxisHelicoid.HelicoidGraphExteriorMetric
import TwoAxisHelicoid.HelicoidGraphModulus

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- An actual embedded C¹ helicoidal graph end does not have a finite
outer circular boundary in isothermal coordinates. Each sufficiently
far spatial point belongs to the same graph by the geometric end
definition. The collar can have any positive finite outer radius. -/
theorem HasHelicoidC1End.no_outer_circle {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (endGraph : HasHelicoidC1End X) (cont : Continuous X)
    {r R : ℝ} (hR : 0<R) (hr : r<R) {Y : ℂ → HelicoidTubeCoordinates}
    (diff : ∀ z : ℂ, r<‖z‖ → ‖z‖<R → DifferentiableAt ℝ Y z)
    (image : ∀ z : ℂ, r<‖z‖ → ‖z‖<R → Y z∈range X)
    (inj : InjOn Y {z | r<‖z‖ ∧ ‖z‖<R})
    (conf : ∀ z : ℂ, r<‖z‖ → ‖z‖<R → ∃ c : ℝ, ∀ v : ℂ,
      (∑ j, (tubeCartesian (fderiv ℝ Y z v) j)^2)=c*‖v‖^2)
    (esc : ∀ B : ℝ, ∃ s<R, ∀ z : ℂ, s<‖z‖ → ‖z‖<R → B<‖Y z‖) : False := by
  obtain ⟨u,B,graph⟩ := endGraph.exterior_conformal_graph cont
  obtain ⟨s,hs,grows⟩ := esc B
  obtain ⟨d,hd,h1,region⟩ := annulusBoundarySector_maps hR (max_lt hr hs)
  let e := annulusBoundarySector R d
  have inRegion (p : ℂ) (hp : p∈openComplexUnitSquare) : r<‖e p‖ ∧ ‖e p‖<R :=
    ⟨(le_max_left r s).trans_lt (region p hp).1,(region p hp).2⟩
  have dr (p : ℂ) := (annulusBoundarySector_hasDerivAt R d p).hasFDerivAt.restrictScalars ℝ
  apply no_finite_width_isothermal_helicoid_graph (u := u) (Y := Y ∘ e)
  · intro p hp
    exact (diff _ (inRegion p hp).1 (inRegion p hp).2).comp p (dr p).differentiableAt
  · exact inj.comp (annulusBoundarySector_injOn hR hd h1) (fun p hp => inRegion p hp)
  · intro p hp
    obtain ⟨c,hc⟩ := conf _ (inRegion p hp).1 (inRegion p hp).2
    let a : ℂ := e p*d
    refine ⟨c*‖a‖^2,fun v => ?_⟩
    have de : fderiv ℝ (Y ∘ e) p v=fderiv ℝ Y (e p) (v*a) :=
      congrArg (fun L : ℂ →L[ℝ] HelicoidTubeCoordinates => L v)
        (((diff _ (inRegion p hp).1 (inRegion p hp).2).hasFDerivAt.comp p (dr p)).fderiv)
    rw [de,hc,norm_mul,mul_pow]
    ring
  · intro p hp
    exact graph (Y (e p)) (image _ (inRegion p hp).1 (inRegion p hp).2)
      (grows _ ((le_max_right r s).trans_lt (region p hp).1) (region p hp).2)
  · intro y hy
    apply tendsto_atTop.mpr
    intro A
    obtain ⟨s',hs',hA⟩ := esc A
    have lower := (annulusBoundarySector_radius_limit hR d y).eventually (lt_mem_nhds hs')
    have ints : ∀ᶠ x : ℝ in 𝓝[<] 1, x∈Ioo (0:ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
    filter_upwards [lower,ints] with x hx hi
    exact (hA _ hx (inRegion ⟨x,y⟩ ⟨hi,hy⟩).2).le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.no_outer_circle
