import TwoAxisHelicoid.MarkedDiskBoundaryBarrier
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology

/-- The marked disk has its ordinary open-disk topology, independently
of the complex atlas of the ambient surface. -/
noncomputable def markedBallPlaneHomeomorph {M : Type*} [TopologicalSpace M] (T : M ≃ₜ ℂ) {R : ℝ} (pos : 0<R) :
    ℂ ≃ₜ markedBallDomain T R :=
  let e := OpenPartialHomeomorph.univBall (E:=ℂ) (0:ℂ) R
  let h := (Homeomorph.Set.univ ℂ).symm.trans ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source (E:=ℂ) (0:ℂ) R).symm).trans e.toHomeomorphSourceTarget)
  (h.trans (Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target (E:=ℂ) (0:ℂ) pos))).trans
    (T.symm.isEmbedding.homeomorphImage (ball 0 R) |>.trans (Homeomorph.setCongr (congrFun T.image_symm (ball 0 R))))

/-- A property valid in a relative neighborhood of every point of the
marking circle holds off one compact set of the open disk. -/
theorem marked_disk_eventually_outside_compact {M : Type*} [TopologicalSpace M] (T : M ≃ₜ ℂ) {R : ℝ}
    {P : markedBallDomain T R → Prop}
    (edge : ∀ p : sphere (0:ℂ) R, ∃ d>0, ∀ x : markedBallDomain T R, dist (T x.val) p.val<d → P x) :
    ∀ᶠ x in cocompact (markedBallDomain T R), P x := by
  classical
  choose r pos covers using edge
  let W := ⋃ p : sphere (0:ℂ) R, ball p.val (r p)
  let K := closedBall (0:ℂ) R \ W
  have ck : IsCompact K := (isCompact_closedBall _ _).diff (isOpen_iUnion fun _ => isOpen_ball)
  have sub : K⊆ball 0 R := by
    intro z hz
    apply lt_of_le_of_ne (mem_closedBall.mp hz.1)
    intro eq
    let p : sphere (0:ℂ) R := ⟨z,eq⟩
    exact hz.2 (mem_iUnion_of_mem p (mem_ball_self (pos p)))
  let j := fun x : markedBallDomain T R => T x.val
  have emb : IsEmbedding j := T.isEmbedding.comp IsEmbedding.subtypeVal
  have cover : K⊆range j := fun z hz => ⟨⟨T.symm z,by change T (T.symm z)∈ball 0 R; rw [T.apply_symm_apply]; exact sub hz⟩,T.apply_symm_apply z⟩
  have compact : IsCompact (j ⁻¹' K) := emb.isCompact_iff.mpr (by rwa [image_preimage_eq_of_subset cover])
  filter_upwards [compact.compl_mem_cocompact] with x away
  have w : j x∈W := by_contra fun nw => away ⟨ball_subset_closedBall x.2,nw⟩
  obtain ⟨p,hp⟩ := mem_iUnion.mp w
  exact covers p x hp

/-- Removing a point from a topological plane preserves connectedness
and yields a noncompact surface. -/
theorem marked_plane_puncture_topology {M : Type*} [TopologicalSpace M] (T : ℂ ≃ₜ M) (p : M) :
    PreconnectedSpace ({p}ᶜ : Set M) ∧ NoncompactSpace ({p}ᶜ : Set M) := by
  have eq : T '' ({T.symm p}ᶜ : Set ℂ)=({p}ᶜ : Set M) := by
    ext x
    rw [T.image_eq_preimage_symm]
    simp only [mem_preimage,mem_compl_iff,mem_singleton_iff,T.symm.injective.eq_iff]
  have pc : IsPreconnected ({p}ᶜ : Set M) := eq ▸ (isConnected_compl_singleton_of_one_lt_rank (E:=ℂ) (by simp) (T.symm p)).isPreconnected.image _ T.continuous.continuousOn
  refine ⟨isPreconnected_iff_preconnectedSpace.mp pc,⟨fun compact => ?_⟩⟩
  have c : IsCompact ({p}ᶜ : Set M) := isCompact_iff_isCompact_univ.mpr compact
  have all := c.union (isCompact_singleton (x:=p))
  rw [compl_union_self] at all
  have cc := all.image T.symm.continuous
  rw [Set.image_univ,T.symm.surjective.range_eq] at cc
  exact NoncompactSpace.noncompact_univ cc

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_disk_eventually_outside_compact
