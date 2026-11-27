import TwoAxisHelicoid.PuncturedChartNeighborhood
import TwoAxisHelicoid.RemovableCoverIsomorphism
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.LocallyConvex

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Every surface point has a coordinate neighborhood inside any prescribed
open set whose intersection with the punctured surface is connected. -/
theorem punctured_surface_coordinate_basis {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace ℂ M]
    (p x : M) (U : Set M) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ (V : Set M) (_ : ℂ ≃ₜ V), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsConnected {v : V | v.1 ≠ p} := by
  have hdim : 1 < Module.rank ℝ ℂ := by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num
  by_cases he : x = p
  · subst x
    let e := (chartAt ℂ p).restrOpen U hU
    obtain ⟨V,H,hV,hpV,hVs,_,hc⟩ := centered_surface_chart_neighborhood hdim e
      (show p ∈ e.source from ⟨mem_chart_source ℂ p,hx⟩)
    exact ⟨V,H,hV,hpV,fun v hv => (hVs hv).2,hc⟩
  · let W := U ∩ ({p}ᶜ : Set M)
    let e := (chartAt ℂ x).restrOpen W (hU.inter isOpen_compl_singleton)
    obtain ⟨V,H,hV,hxV,hVs,_⟩ := centered_euclidean_chart_neighborhood e
      (show x ∈ e.source from ⟨mem_chart_source ℂ x,hx,he⟩)
    let _ : ConnectedSpace V := H.surjective.connectedSpace H.continuous
    refine ⟨V,H,hV,hxV,fun v hv => (hVs hv).2.1,?_⟩
    have hfull : {v : V | v.1 ≠ p} = univ := eq_univ_of_forall fun v => (hVs v.2).2.2
    rw [hfull]
    exact isConnected_univ

/-- Real angle coordinates can be chosen in every open neighborhood on
the circle, directly from its exponential covering. -/
theorem spin_angle_coordinate_basis (a : Circle) (U : Set Circle) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ (V : Set Circle) (_ : ℝ ≃ₜ V), IsOpen V ∧ a ∈ V ∧ V ⊆ U := by
  obtain ⟨t,ht⟩ := Circle.exp_surjective a
  obtain ⟨j,hj,he⟩ := Circle.isCoveringMap_exp.isLocalHomeomorph t
  have hja : j t = a := (congrFun he t).symm.trans ht
  let e := j.symm.restrOpen U hU
  obtain ⟨V,H,hV,haV,hVe,_⟩ := centered_euclidean_chart_neighborhood e
    (show a ∈ e.source from ⟨hja ▸ j.map_source hj,ha⟩)
  exact ⟨V,H,hV,haV,fun v hv => (hVe hv).2⟩

/-- Removing the full circle of frames over one point of a compact or
noncompact marked surface satisfies the actual removable-cover criterion. -/
theorem punctured_surface_times_circle_removable
    {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace ℂ M] (p : M) :
    HasRemovableCoverBasis {z : M × Circle | z.1 ≠ p} := by
  rintro ⟨x,a⟩ U hU hx
  obtain ⟨W,T,hW,hT,hxW,haT,hWT⟩ := isOpen_prod_iff.mp hU x a hx
  obtain ⟨V,H,hV,hxV,hVW,hc⟩ := punctured_surface_coordinate_basis p x W hW hxW
  obtain ⟨S,A,hS,haS,hST⟩ := spin_angle_coordinate_basis a T hT haT
  let J := Homeomorph.Set.prod V S
  let G : ℂ × ℝ ≃ₜ (V ×ˢ S) := (H.prodCongr A).trans J.symm
  let _ : ConnectedSpace S := A.surjective.connectedSpace A.continuous
  refine ⟨V ×ˢ S,hV.prod hS,⟨hxV,haS⟩,(prod_mono hVW hST).trans hWT,
    G.symm.toHomotopyEquiv.simplyConnectedSpace,G.isQuotientMap.locallyPathConnectedSpace,?_⟩
  have he : {z : (V ×ˢ S) | z.1.1 ≠ p} = J ⁻¹' ({v : V | v.1 ≠ p} ×ˢ (univ : Set S)) := by
    ext z
    change (z.1.1 ≠ p) ↔ (z.1.1 ≠ p ∧ True)
    simp
  change IsConnected {z : (V ×ˢ S) | z.1.1 ≠ p}
  rw [he]
  exact J.isConnected_preimage.mpr (hc.prod isConnected_univ)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_surface_times_circle_removable
