import TwoAxisHelicoid.SmoothImmersionLeftInverse
import TwoAxisHelicoid.FirstContactGraphOrdering

namespace TwoAxisHelicoid
open Filter Set Topology
open scoped Topology ContDiff

/-- Keeping the multiplier as the first coordinate preserves immersion
rank precisely when the spatial slice has injective derivative. -/
private theorem parameter_graph_has_injective_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : ℝ × E → F} {t : ℝ} {u : E} (hh : DifferentiableAt ℝ H (t,u))
    (hi : Function.Injective (fderiv ℝ (fun w => H (t,w)) u)) :
    let J := (ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ H (t,u))
    HasFDerivAt (fun q : ℝ × E => (q.1,H q)) J (t,u) ∧ Function.Injective J := by
  let D := fderiv ℝ H (t,u)
  let J := (ContinuousLinearMap.fst ℝ ℝ E).prod D
  have hfix : HasFDerivAt (fun w : E => (t,w)) ((0:E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) u :=
    (hasFDerivAt_const t u).prodMk (hasFDerivAt_id u)
  have frozen (v : E) : fderiv ℝ (fun w => H (t,w)) u v=D (0,v) :=
    congrArg (fun L : E →L[ℝ] F => L v) (hh.hasFDerivAt.comp u hfix).fderiv
  refine ⟨(ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.prodMk hh.hasFDerivAt,?_⟩
  rintro ⟨s,x⟩ ⟨v,y⟩ e
  have fst : s=v := congrArg Prod.fst e
  subst v
  refine Prod.ext rfl (hi ?_)
  rw [frozen,frozen]
  have eq : D (s,x)=D (s,y) := congrArg Prod.snd e
  have split (p : E) : D (s,p)=D (s,0)+D (0,p) := by rw [← map_add]; simp
  rw [split x,split y] at eq
  exact add_left_cancel eq

/-- In a smooth one-parameter immersion family an ordinary chart stays
one-to-one for all nearby multipliers on the same source neighborhood. -/
theorem parameterized_immersion_locally_injective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
    {H : ℝ × E → F} {t : ℝ} {u : E} (hh : AnalyticAt ℝ H (t,u))
    (hi : Function.Injective (fderiv ℝ (fun w => H (t,w)) u)) :
    ∃ V ∈ 𝓝 t, ∃ U ∈ 𝓝 u, ∀ s ∈ V, InjOn (fun w => H (s,w)) U := by
  let G := fun q : ℝ × E => (q.1,H q)
  have ha : AnalyticAt ℝ G (t,u) := ((ContinuousLinearMap.fst ℝ ℝ E).analyticAt _).prod hh
  obtain ⟨hd,inj⟩ := parameter_graph_has_injective_derivative hh.differentiableAt hi
  obtain ⟨g,W,op,hw,_,inv⟩ := smooth_local_left_inverse (show ContDiffAt ℝ ∞ G (t,u) from ha.contDiffAt)
    (hd.fderiv.symm ▸ inj)
  have hW := op.mem_nhds hw
  rw [nhds_prod_eq] at hW
  obtain ⟨V,hV,U,hU,sub⟩ := Filter.mem_prod_iff.mp hW
  refine ⟨V,hV,U,hU,?_⟩
  intro s hs x hx y hy eq
  have e : G (s,x)=G (s,y) := Prod.ext rfl eq
  exact congrArg Prod.snd ((inv _ (sub ⟨hs,hx⟩)).symm.trans ((congrArg g e).trans (inv _ (sub ⟨hs,hy⟩))))

/-- The inverse to a nonsingular spatial projection depends analytically
on both the multiplier and the projected point. The first coordinate of
the change of variables is the multiplier itself. -/
theorem parameterized_analytic_projection_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] {H : ℝ × E → E} {t : ℝ} {u : E}
    (hh : AnalyticAt ℝ H (t,u)) (hi : Function.Injective (fderiv ℝ (fun w => H (t,w)) u)) :
    ∃ e : OpenPartialHomeomorph (ℝ × E) (ℝ × E), (e : ℝ × E → ℝ × E)=(fun q => (q.1,H q)) ∧
      (t,u) ∈ e.source ∧ AnalyticAt ℝ e.symm (t,H (t,u)) := by
  let G := fun q : ℝ × E => (q.1,H q)
  let J := (ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ H (t,u))
  have ha : ContDiffAt ℝ ω G (t,u) := (((ContinuousLinearMap.fst ℝ ℝ E).analyticAt _).prod hh).contDiffAt
  obtain ⟨hd,inj⟩ := parameter_graph_has_injective_derivative hh.differentiableAt hi
  let D := (LinearEquiv.ofBijective J.toLinearMap ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩).toContinuousLinearEquiv
  have hD : HasFDerivAt G (D : (ℝ × E) →L[ℝ] (ℝ × E)) (t,u) := hd
  let e := ha.toOpenPartialHomeomorph G hD (by simp)
  exact ⟨e,rfl,ha.mem_toOpenPartialHomeomorph_source hD (by simp),(ha.to_localInverse hD (by simp)).analyticAt⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.parameterized_immersion_locally_injective
#print axioms TwoAxisHelicoid.parameterized_analytic_projection_chart
