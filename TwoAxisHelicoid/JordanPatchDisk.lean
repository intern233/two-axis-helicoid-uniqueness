import TwoAxisHelicoid.CompactChartPatchBoundary
import Mathlib.Analysis.Normed.Module.Connected

namespace TwoAxisHelicoid
open Set Metric Topology

/-- The usual classification of connected compact real one-manifolds
without boundary. The curve has its subspace topology. -/
def CompactRealCurveClassification : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [ChartedSpace ℝ M],
    Nonempty (M ≃ₜ sphere (0:ℂ) 1)

/-- Ambient planar Jordan–Schönflies, with no prescribed behavior of
the parametrization of the circle. -/
def PlanarSchoenfliesTheorem : Prop :=
  ∀ (γ : sphere (0:ℂ) 1 → ℂ), IsEmbedding γ → ∃ F : ℂ ≃ₜ ℂ, F '' range γ=sphere 0 1

/-- Among the two sides of a round circle, the relatively compact
open domain with that boundary must be the open unit ball. -/
theorem bounded_domain_with_round_frontier {V : Set ℂ} (op : IsOpen V) (nv : V.Nonempty)
    (compact : IsCompact (closure V)) (edge : frontier V=sphere 0 1) : V=ball 0 1 := by
  have split {S : Set ℂ} (con : IsPreconnected S) (away : Disjoint S (sphere 0 1)) :
      S⊆V ∨ S⊆(closure V)ᶜ := by
    apply isPreconnected_iff_subset_of_disjoint.mp con V (closure V)ᶜ op isClosed_closure.isOpen_compl
    · intro z hz
      by_cases h : z∈V
      · exact Or.inl h
      · exact Or.inr (fun cl => disjoint_left.mp away hz (edge ▸ (show z∈frontier V from ⟨cl,fun hi => h (interior_subset hi)⟩)))
    · rw [show V∩(closure V)ᶜ=∅ from (disjoint_compl_right.mono_left subset_closure).inter_eq,inter_empty]
  let T := {z : ℂ | 1<‖z‖}
  have far := split (complex_norm_exterior_isPreconnected (show (0:ℝ)≤1 by norm_num))
    (show Disjoint T (sphere 0 1) from disjoint_left.mpr fun z hz hs => (ne_of_gt hz) (mem_sphere_zero_iff_norm.mp hs))
  have outside : T⊆(closure V)ᶜ := far.resolve_left (by
    intro all
    obtain ⟨B,bd⟩ := compact.isBounded.exists_norm_le
    let x := max B 1+1
    have pos : 0<x := by dsimp [x]; linarith [le_max_right B 1]
    have size : ‖(x:ℂ)‖=x := by rw [Complex.norm_real,Real.norm_of_nonneg pos.le]
    have hx : (x:ℂ)∈T := by change 1<‖(x:ℂ)‖; rw [size]; dsimp [x]; linarith [le_max_right B 1]
    have n := bd (x:ℂ) (subset_closure (all hx))
    rw [size] at n
    dsimp [x] at n
    linarith [le_max_left B 1])
  have into : V⊆ball 0 1 := by
    intro z hz
    rw [mem_ball_zero_iff]
    apply lt_of_le_of_ne (le_of_not_gt (fun h => outside h (subset_closure hz)))
    intro eq
    have on : z∈frontier V := edge.symm ▸ (mem_sphere_zero_iff_norm.mpr eq)
    exact on.2 (op.interior_eq.symm ▸ hz)
  have inner := split (convex_ball (0:ℂ) 1).isPreconnected
    (show Disjoint (ball (0:ℂ) 1) (sphere 0 1) from disjoint_left.mpr fun z hz hs =>
      (mem_ball_zero_iff.mp hz).ne (mem_sphere_zero_iff_norm.mp hs))
  obtain ⟨z,hz⟩ := nv
  exact into.antisymm (inner.resolve_right fun miss => miss (into hz) (subset_closure hz))

/-- After the standard topological classification of a real curve
and planar Schönflies, the homeomorphism identifies both the filled
patch and its exact open interior with the closed and open unit disk. -/
theorem jordan_patch_is_closed_disk (circle : CompactRealCurveClassification) (schoen : PlanarSchoenfliesTheorem)
    {W : Set ℂ} (ow : IsOpen W) (non : W.Nonempty) (kw : IsCompact (closure W))
    (boundary : IsConnected (frontier W)) (atlas : Nonempty (ChartedSpace ℝ (frontier W))) :
    ∃ D : closedBall (0:ℂ) 1 ≃ₜ closure W, ∀ z, z.1∈ball (0:ℂ) 1 ↔ (D z).1∈W := by
  let _ := atlas.some
  let _ : CompactSpace (frontier W) := isCompact_iff_compactSpace.mp (kw.of_isClosed_subset isClosed_frontier frontier_subset_closure)
  let _ : ConnectedSpace (frontier W) := isConnected_iff_connectedSpace.mp boundary
  obtain ⟨g⟩ := circle (frontier W)
  let γ := (Subtype.val : frontier W → ℂ) ∘ g.symm
  obtain ⟨F,round⟩ := schoen γ (Topology.IsEmbedding.subtypeVal.comp g.symm.isEmbedding)
  have rg : range γ=frontier W := by dsimp only [γ]; rw [range_comp,g.symm.surjective.range_eq,Set.image_univ,Subtype.range_coe]
  rw [rg, F.image_frontier] at round
  have closed := kw.image F.continuous
  rw [F.image_closure] at closed
  have disk := bounded_domain_with_round_frontier (F.isOpenMap W ow) (non.image F) closed round
  have filled : F '' closure W=closedBall 0 1 := by rw [F.image_closure,disk,closure_ball (0:ℂ) one_ne_zero]
  let h := F.isEmbedding.homeomorphImage (closure W)
  let D := (h.trans (Homeomorph.setCongr filled)).symm
  refine ⟨D,fun z => ?_⟩
  have eq : F (D z).1=z.1 := congrArg Subtype.val ((h.trans (Homeomorph.setCongr filled)).apply_symm_apply z)
  rw [← disk,← eq]
  exact F.injective.mem_set_image

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_domain_with_round_frontier
#print axioms TwoAxisHelicoid.jordan_patch_is_closed_disk
