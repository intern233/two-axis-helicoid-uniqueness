import TwoAxisHelicoid.ContactSheetGraphOrdering
import TwoAxisHelicoid.ConformalMinimalGraphContact

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology

/-- Freezing the parameter of a regular moving harmonic conformal
graph gives a full neighborhood of solutions of the minimal graph PDE. -/
theorem AnalyticContactSheet.minimal_graph {F : ℝ × ℂ → Fin 3 → ℝ} {t : ℝ} {b : ℂ}
    (B : AnalyticContactSheet F t b) (hf : AnalyticAt ℝ F (t,b))
    (reg : ∀ᶠ v in 𝓝 b, (∀ j, HarmonicAt (fun u => F (t,u) j) v) ∧ ConformalCoordinateDerivatives (fun u => F (t,u)) v)
    (hn : horizontalMinor (planePartial 1 (fun u => F (t,u)) b) (planePartial I (fun u => F (t,u)) b) ≠ 0) :
    ∀ᶠ p in 𝓝 (spatialGraphProjection 0 1 (F (t,b))), cartesianMinimalGraphOperator (fun w => B.height (t,w)) p=0 := by
  let P := spatialGraphProjection 0 1
  let X := fun u => F (t,u)
  let w := P (X b)
  let g := fun p => B.height (t,p)
  let inv := fun p => B.inv (t,p)
  have ax : AnalyticAt ℝ X b := hf.comp (analyticAt_const.prod analyticAt_id)
  have ag : AnalyticAt ℝ g w := (B.analytic_height hf).comp (analyticAt_const.prod analyticAt_id)
  have invt : Tendsto inv (𝓝 w) (𝓝 b) := B.center ▸ (B.analytic.comp (analyticAt_const.prod analyticAt_id)).continuousAt.tendsto
  have fixed (u : ℂ) : ContinuousAt (fun v : ℂ => (t,v)) u := continuousAt_const.prodMk continuousAt_id
  have left : ∀ᶠ u in 𝓝 b, X u 2=g (P (X u)) :=
    ((fixed b).eventually B.left_inv).mono (fun u e => congrArg (fun v => X v 2) e.symm)
  have right : ∀ᶠ p in 𝓝 w, P (X (inv p))=p := (fixed w).eventually B.right_inv
  have aa := planePartial_analyticAt ax 1
  have ba := planePartial_analyticAt ax I
  have minor : ContinuousAt (fun u => horizontalMinor (planePartial 1 X u) (planePartial I X u)) b :=
    ((((analyticAt_pi_iff.mp aa) 0).mul ((analyticAt_pi_iff.mp ba) 1)).sub
      (((analyticAt_pi_iff.mp ba) 0).mul ((analyticAt_pi_iff.mp aa) 1))).continuousAt
  filter_upwards [right,ag.eventually_analyticAt,invt.eventually reg,invt.eventually (eventually_eventually_nhds.mpr left),
    invt.eventually (minor.eventually_ne hn)] with p eq ana hreg onGraph nonsing
  rw [← eq] at ana ⊢
  exact harmonic_immersion_graph_operator_zero hreg.1 hreg.2 ana nonsing onGraph

/-- At the first contact of two previously separated one-parameter
families of regular minimal sheets with a common horizontal projection,
each point sufficiently near the contact on the first sheet lies on
the second sheet in any prescribed neighborhood of its parameter. -/
theorem minimal_contact_sheet_germs_coincide {F G : ℝ × ℂ → Fin 3 → ℝ} {t : ℝ} {a b : ℂ}
    (fa : AnalyticAt ℝ F (t,a)) (gb : AnalyticAt ℝ G (t,b)) (same : F (t,a)=G (t,b))
    (hF : ∀ᶠ v in 𝓝 a, (∀ j, HarmonicAt (fun u => F (t,u) j) v) ∧ ConformalCoordinateDerivatives (fun u => F (t,u)) v)
    (hG : ∀ᶠ v in 𝓝 b, (∀ j, HarmonicAt (fun u => G (t,u) j) v) ∧ ConformalCoordinateDerivatives (fun u => G (t,u)) v)
    (hi : Function.Injective (fderiv ℝ (fun u => F (t,u)) a))
    (A : AnalyticContactSheet F t a) (B : AnalyticContactSheet G t b)
    (hn : horizontalMinor (planePartial 1 (fun u => G (t,u)) b) (planePartial I (fun u => G (t,u)) b) ≠ 0)
    {U V : Set ℂ} (hu : U ∈ 𝓝 a) (hv : V ∈ 𝓝 b)
    (sep : ∃ᶠ s in 𝓝 t, ∀ u ∈ U, ∀ v ∈ V, F (s,u) ≠ G (s,v)) :
    ∀ᶠ u in 𝓝 a, F (t,u) ∈ (fun v => G (t,v)) '' V := by
  let P := spatialGraphProjection 0 1
  let X := fun u => F (t,u)
  let w := P (X a)
  let g := fun p => B.height (t,p)
  have wb : P (G (t,b))=w := congrArg P same.symm
  have ax : AnalyticAt ℝ X a := fa.comp (analyticAt_const.prod analyticAt_id)
  have cp : ContinuousAt (P ∘ X) a := P.continuous.continuousAt.comp ax.continuousAt
  have tfix (v : ℂ) : ContinuousAt (fun p : ℂ => (t,p)) v := continuousAt_const.prodMk continuousAt_id
  have ag : AnalyticAt ℝ g w := wb ▸ (B.analytic_height gb).comp (analyticAt_const.prod analyticAt_id)
  have model := B.minimal_graph gb hG hn
  rw [show spatialGraphProjection 0 1 (G (t,b))=w from wb] at model
  have eqA : ∀ᶠ u in 𝓝 a, X u 2=A.height (t,P (X u)) :=
    ((tfix a).eventually A.left_inv).mono (fun u e => congrArg (fun v => X v 2) e.symm)
  have valB : g w=G (t,b) 2 := by change G (t,B.inv (t,w)) 2=G (t,b) 2; rw [← wb,B.center]
  have touch : immersionGraphDifference X g a=0 := sub_eq_zero.mpr ((congrFun same 2).trans valB.symm)
  have order := contact_sheet_graphs_ordered fa gb same A B hu hv sep
  have side : (∀ᶠ u in 𝓝 a, 0 ≤ immersionGraphDifference X g u) ∨ (∀ᶠ u in 𝓝 a, immersionGraphDifference X g u ≤ 0) := by
    rcases order with l | r
    · right
      filter_upwards [eqA,cp.eventually l] with u e h
      exact sub_nonpos.mpr (e.trans_le h)
    · left
      filter_upwards [eqA,cp.eventually r] with u e h
      exact sub_nonneg.mpr (e.symm ▸ h)
  have coincidence := harmonic_immersion_one_sided_minimal_graph hF hi ag model touch side
  have right : ∀ᶠ p in 𝓝 w, P (G (t,B.inv (t,p)))=p := by rw [← wb]; exact (tfix _).eventually B.right_inv
  have n : ∀ᶠ p in 𝓝 w, B.inv (t,p) ∈ V := by
    rw [← wb]
    have tend : Tendsto (fun p : ℂ => B.inv (t,p)) (𝓝 (P (G (t,b)))) (𝓝 b) :=
      by
        have h : Tendsto (fun p : ℂ => B.inv (t,p)) (𝓝 (P (G (t,b)))) (𝓝 (B.inv (t,spatialGraphProjection 0 1 (G (t,b))))) :=
          (B.analytic.comp (analyticAt_const.prod analyticAt_id)).continuousAt.tendsto
        rwa [B.center] at h
    exact tend.eventually hv
  filter_upwards [coincidence,cp.eventually right,cp.eventually n] with u heights proj inside
  exact ⟨B.inv (t,P (X u)),inside,eq_of_cartesian_graph_data proj heights.symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.AnalyticContactSheet.minimal_graph
#print axioms TwoAxisHelicoid.minimal_contact_sheet_germs_coincide
