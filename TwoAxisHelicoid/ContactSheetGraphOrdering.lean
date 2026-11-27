import TwoAxisHelicoid.AnalyticContactSheet
import TwoAxisHelicoid.FirstContactGraphOrdering
import Mathlib.Analysis.Normed.Module.Convex

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology

theorem eq_of_cartesian_graph_data {u v : Fin 3 → ℝ}
    (h : spatialGraphProjection 0 1 u=spatialGraphProjection 0 1 v) (e : u 2=v 2) : u=v := by
  funext j
  fin_cases j
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h
  · exact e

/-- A common nonsingular projection turns cofinal separation of two
parametrized patches into a one-sided order for their actual height
functions on a neighborhood of the limiting spatial point. -/
theorem contact_sheet_graphs_ordered {F G : ℝ × ℂ → Fin 3 → ℝ} {t : ℝ} {a b : ℂ}
    (fa : AnalyticAt ℝ F (t,a)) (gb : AnalyticAt ℝ G (t,b)) (same : F (t,a)=G (t,b))
    (A : AnalyticContactSheet F t a) (B : AnalyticContactSheet G t b)
    {U V : Set ℂ} (hu : U ∈ 𝓝 a) (hv : V ∈ 𝓝 b)
    (separate : ∃ᶠ s in 𝓝 t, ∀ u ∈ U, ∀ v ∈ V, F (s,u) ≠ G (s,v)) :
    let w := spatialGraphProjection 0 1 (F (t,a))
    (∀ᶠ p in 𝓝 w, A.height (t,p) ≤ B.height (t,p)) ∨
      (∀ᶠ p in 𝓝 w, B.height (t,p) ≤ A.height (t,p)) := by
  let P := spatialGraphProjection 0 1
  let w := P (F (t,a))
  have wB : P (G (t,b))=w := congrArg P same.symm
  have hA : AnalyticAt ℝ A.height (t,w) := A.analytic_height fa
  have hB : AnalyticAt ℝ B.height (t,w) := wB ▸ B.analytic_height gb
  have rA := A.right_inv
  have rB : ∀ᶠ q in 𝓝 (t,w), P (G (q.1,B.inv q))=q.2 := wB ▸ B.right_inv
  have nA : ∀ᶠ q in 𝓝 (t,w), A.inv q ∈ U :=
    A.analytic.continuousAt.eventually (A.center.symm ▸ hu)
  have nB : ∀ᶠ q in 𝓝 (t,w), B.inv q ∈ V := by
    rw [← wB]
    exact B.analytic.continuousAt.eventually (B.center.symm ▸ hv)
  let S := {q : ℝ × ℂ | A.inv q ∈ U ∧ B.inv q ∈ V ∧ P (F (q.1,A.inv q))=q.2 ∧
    P (G (q.1,B.inv q))=q.2 ∧ ContinuousAt A.height q ∧ ContinuousAt B.height q}
  have nh : S ∈ 𝓝 (t,w) := by
    filter_upwards [nA,nB,rA,rB,hA.eventually_analyticAt,hB.eventually_analyticAt] with q au bv ar br ca cb
    exact ⟨au,bv,ar,br,ca.continuousAt,cb.continuousAt⟩
  rw [nhds_prod_eq] at nh
  obtain ⟨J,hJ,D,hD,inside⟩ := Filter.mem_prod_iff.mp nh
  obtain ⟨r,hr,ballSub⟩ := Metric.mem_nhds_iff.mp hD
  let ball := Metric.ball w r
  have product (s : ℝ) (hs : s ∈ J) (p : ℂ) (hp : p ∈ ball) : (s,p) ∈ S := inside ⟨hs,ballSub hp⟩
  have limitCont (p : ℂ) (hp : p ∈ ball) := product t (mem_of_mem_nhds hJ) p hp
  have order := graph_sheets_ordered_at_first_contact (convex_ball w r).isPreconnected
    (fun s p => A.height (s,p)) (fun s p => B.height (s,p)) t
    (fun p hp => (limitCont p hp).2.2.2.2.1.comp (x := t) (f := fun s : ℝ => (s,p)) (by fun_prop))
    (fun p hp => (limitCont p hp).2.2.2.2.2.comp (x := t) (f := fun s : ℝ => (s,p)) (by fun_prop))
    ((separate.and_eventually hJ).mono (by
      rintro s ⟨sep,hs⟩
      refine ⟨fun p hp => ((product s hs p hp).2.2.2.2.1.comp (x := p) (f := fun p : ℂ => (s,p)) (by fun_prop)).continuousWithinAt,
        fun p hp => ((product s hs p hp).2.2.2.2.2.comp (x := p) (f := fun p : ℂ => (s,p)) (by fun_prop)).continuousWithinAt,?_⟩
      intro p hp eq
      have data := product s hs p hp
      exact sep _ data.1 _ data.2.1 (eq_of_cartesian_graph_data (data.2.2.1.trans data.2.2.2.1.symm) eq)))
  exact order.imp (fun h => Filter.mem_of_superset (ball_mem_nhds w hr) h) (fun h => Filter.mem_of_superset (ball_mem_nhds w hr) h)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.contact_sheet_graphs_ordered
