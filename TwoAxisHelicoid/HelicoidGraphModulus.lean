import TwoAxisHelicoid.FiniteWidthConformalObstruction
import TwoAxisHelicoid.HelicoidConformalExteriorParameter
import TwoAxisHelicoid.ConformalPlaneDistortion

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A sector of a finite-modulus annulus cannot conformally parametrize
an escaping sector of a helicoidal C¹ normal graph. Both the projection
and its distortion are derived from the actual spatial parametrization. -/
theorem no_finite_width_isothermal_helicoid_graph
    {u : ℝ × ℝ → ℝ} {Y : ℂ → HelicoidTubeCoordinates}
    (diff : ∀ p∈openComplexUnitSquare, DifferentiableAt ℝ Y p)
    (inj : InjOn Y openComplexUnitSquare)
    (isothermal : ∀ p∈openComplexUnitSquare, ∃ c : ℝ, ∀ v : ℂ,
      (∑ j, (tubeCartesian (fderiv ℝ Y p v) j)^2)=c*‖v‖^2)
    (graph : ∀ p∈openComplexUnitSquare, ∃ z : ℂ, 2<‖z‖ ∧
      DifferentiableAt ℝ u (helicoidConformalBase z) ∧ |u (helicoidConformalBase z)|≤1/2 ∧
      helicoidGraphGradientNorm u (helicoidConformalBase z)≤1/2 ∧
      Y p=helicoidGraphMap u (helicoidConformalBase z))
    (escape : ∀ y ∈ Ioo (0:ℝ) 1, Tendsto (fun x : ℝ => ‖Y ⟨x,y⟩‖) (𝓝[<] 1) atTop) : False := by
  let F := helicoidProjectedComplexParameter ∘ Y
  let G := helicoidGraphMap u ∘ helicoidConformalBase
  have data (p : ℂ) (hp : p∈openComplexUnitSquare) :
      2<‖F p‖ ∧ DifferentiableAt ℝ u (helicoidConformalBase (F p)) ∧ |u (helicoidConformalBase (F p))|≤1/2 ∧
      helicoidGraphGradientNorm u (helicoidConformalBase (F p))≤1/2 ∧ Y p=G (F p) ∧ Y p∈helicoidTubeEquiv.target := by
    obtain ⟨z,hz,du,small,gr,eq⟩ := graph p hp
    have fact := helicoidProjectedComplexParameter_graph (small.trans_lt (by norm_num : (1/2:ℝ)<1))
    have value : F p=z := (congrArg helicoidProjectedComplexParameter eq).trans fact.2
    rw [value]
    exact ⟨hz,du,small,gr,eq,eq ▸ fact.1⟩
  have fd (p : ℂ) (hp : p∈openComplexUnitSquare) : DifferentiableAt ℝ F p :=
    (helicoidProjectedComplexParameter_differentiable (data p hp).2.2.2.2.2).comp p (diff p hp)
  have fi : InjOn F openComplexUnitSquare := by
    intro p hp q hq e
    exact inj hp hq ((data p hp).2.2.2.2.1.trans ((congrArg G e).trans (data q hq).2.2.2.2.1.symm))
  have square : IsOpen openComplexUnitSquare :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage Complex.equivRealProdCLM.continuous
  apply no_finite_width_escaping_plane_chart fd fi (fun p hp => (data p hp).1) (K := 4)
  · intro p hp
    obtain ⟨_,du,small,gr,_,_⟩ := data p hp
    obtain ⟨c,hc⟩ := isothermal p hp
    have gd := (helicoidGraphMap_differentiableAt du).comp (F p) (helicoidConformalBase_hasFDerivAt _).differentiableAt
    have coincide : Y =ᶠ[𝓝 p] G ∘ F := by
      filter_upwards [square.mem_nhds hp] with q hq using (data q hq).2.2.2.2.1
    have d : fderiv ℝ Y p=(fderiv ℝ G (F p)).comp (fderiv ℝ F p) :=
      coincide.fderiv_eq.trans (fderiv_comp p gd (fd p hp))
    apply horizontal_distortion_of_conformal_bounds (c := c) (m := (Real.cosh (F p).re)^2) _ (by positivity)
    intro v
    have h := helicoid_conformal_graph_metric_bounds du small gr (fderiv ℝ F p v)
    have iso := hc v
    rw [d] at iso
    exact ⟨h.1.trans_eq iso,iso.symm.trans_le h.2⟩
  · intro y hy
    apply bounded_helicoid_graph_escape (s := fun t : ℝ => u (helicoidConformalBase (F ⟨t,y⟩)))
      (Y := fun t : ℝ => Y ⟨t,y⟩) _ (escape y hy)
    have ints : ∀ᶠ t : ℝ in 𝓝[<] 1, t∈Ioo (0:ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
    filter_upwards [ints] with t ht
    have h := data ⟨t,y⟩ ⟨ht,hy⟩
    exact ⟨h.2.2.1.trans (by norm_num),h.2.2.2.2.1⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.no_finite_width_isothermal_helicoid_graph
