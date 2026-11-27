import TwoAxisHelicoid.RegularCutHalfPlaneCharts
import TwoAxisHelicoid.RegularBoundaryManifold
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

namespace TwoAxisHelicoid
open Set Complex Filter Topology
open scoped Topology ContDiff

private theorem map_nhds_of_chart {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} (cf : ContinuousAt f x) (e : OpenPartialHomeomorph Y ℝ)
    (hx : f x∈e.source) (onto : map (e ∘ f) (𝓝 x)=𝓝 (e (f x))) :
    map f (𝓝 x)=𝓝 (f x) := by
  have eq : (e.symm ∘ (e ∘ f)) =ᶠ[𝓝 x] f :=
    (cf.eventually (e.open_source.mem_nhds hx)).mono (fun y hy => e.left_inv hy)
  calc map f (𝓝 x)=map (e.symm ∘ (e ∘ f)) (𝓝 x) := Filter.map_congr eq.symm
       _=map e.symm (map (e ∘ f) (𝓝 x)) := Filter.map_map.symm
       _=𝓝 (f x) := by rw [onto,e.symm.map_nhds_eq (e.map_source hx),e.left_inv hx]

/-- A C¹ curve moving at nonzero speed on a regular planar height fiber
is open as a map to that fiber. The level coordinate and the inverse of
the one-dimensional time coordinate are both constructed locally. -/
theorem regular_height_trajectory_isOpenMap {h : ℂ → ℝ} {v : ℝ} {γ : ℝ → ℂ}
    (smooth : ContDiff ℝ 1 γ) (onLevel : ∀ t, h (γ t)=v)
    (regular : ∀ t, ContDiffAt ℝ ∞ h (γ t) ∧ ∃ w, fderiv ℝ h (γ t) w≠0)
    (moving : ∀ t, deriv γ t≠0) :
    IsOpenMap (fun t => (⟨γ t,onLevel t⟩ : h ⁻¹' {v})) := by
  let S := h ⁻¹' {v}
  let g : ℝ → S := fun t => ⟨γ t,onLevel t⟩
  have cg : Continuous g := smooth.continuous.subtype_mk _
  apply isOpenMap_iff_nhds_le.mpr
  intro t
  have sub := ((regular t).1.differentiableAt (by simp)).hasFDerivAt.sub_const v
  obtain ⟨e,inside,first,de,back⟩ := regular_real_level_coordinate ((regular t).1.sub contDiffAt_const)
    (sub.fderiv ▸ (regular t).2)
  have line : e.IsImage S ({0} ×ˢ (univ : Set ℝ)) := by
    intro z _
    change ((e z).1=0 ∧ (e z).2∈(univ : Set ℝ)) ↔ h z=v
    rw [first]; simp [sub_eq_zero]
  obtain ⟨a,chart,coord⟩ := line_chart_on_slice (g t) e inside line
  have de' := (de.differentiableAt (by simp)).hasFDerivAt
  have inv := (back.differentiableAt (by simp)).hasFDerivAt.comp (γ t) de'
  have eqId : e.symm ∘ e =ᶠ[𝓝 (γ t)] id :=
    Filter.mem_of_superset (e.open_source.mem_nhds inside) (fun z hz => e.left_inv hz)
  have ident := inv.fderiv.symm.trans (eqId.fderiv_eq (𝕜:=ℝ))
  have dg := de'.comp_hasDerivAt t ((smooth.differentiable one_ne_zero t).hasDerivAt)
  have fst : HasDerivAt (fun s => (e (γ s)).1) ((fderiv ℝ e (γ t)) (deriv γ t)).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t dg
  have snd : HasDerivAt (fun s => (e (γ s)).2) ((fderiv ℝ e (γ t)) (deriv γ t)).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t dg
  have h0 : (fun s => (e (γ s)).1)=(fun _ : ℝ => (0:ℝ)) := funext (fun s => by rw [first,onLevel,sub_self])
  have fst0 : ((fderiv ℝ e (γ t)) (deriv γ t)).1=0 := fst.unique (h0.symm ▸ hasDerivAt_const t (0:ℝ))
  let u := fun s : ℝ => (e (γ s)).2
  have sc : ContDiffAt ℝ 1 u t := (de.of_le (by simp) |>.comp t smooth.contDiffAt).snd
  have sndNZ : deriv u t≠0 := by
    intro bad
    have zero : fderiv ℝ e (γ t) (deriv γ t)=0 := Prod.ext fst0 (snd.deriv.symm.trans bad)
    have applied := DFunLike.congr_fun ident (deriv γ t)
    rw [ContinuousLinearMap.comp_apply,zero,map_zero,fderiv_id,ContinuousLinearMap.id_apply] at applied
    exact moving t applied.symm
  have equal : a ∘ g =ᶠ[𝓝 t] u :=
    Filter.mem_of_superset (cg.continuousAt (x:=t) (a.open_source.mem_nhds chart)) (fun s hs => coord (g s) hs)
  have onto : map (a ∘ g) (𝓝 t)=𝓝 (a (g t)) := by
    rw [Filter.map_congr equal,show a (g t)=u t from equal.self_of_nhds]
    exact (sc.hasStrictDerivAt one_ne_zero).map_nhds_eq sndNZ
  exact (map_nhds_of_chart cg.continuousAt a chart onto).ge

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_height_trajectory_isOpenMap
