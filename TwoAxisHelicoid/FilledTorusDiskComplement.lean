import TwoAxisHelicoid.TranslatedPlaneFill
import TwoAxisHelicoid.ConnectedPlaneComplementDisk
import TwoAxisHelicoid.TorusEmbeddedDiskLift
import TwoAxisHelicoid.CompactPlanarChartComplement
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

namespace TwoAxisHelicoid
open Set Metric Bornology Topology

/-- A bounded connected neighborhood on which a lattice quotient is
injective stays injective after all its bounded holes are filled. -/
theorem filled_torus_lift_chart (L : PeriodPair) {O : Set ℂ}
    (opened : IsOpen O) (connected : IsConnected O) (bounded : IsBounded O)
    (injective : InjOn (periodTorusProjection L) O) :
    ∃ j : ℂ → PeriodTorus L, IsOpenEmbedding j ∧ periodTorusProjection L '' O⊆range j := by
  let F := boundedPlaneFill O
  obtain ⟨inc,size,outside,ofill,cfill⟩ := boundedPlaneFill_properties bounded
  have fo : IsOpen F := ofill opened
  have fc : IsConnected F := cfill opened connected
  obtain ⟨disk⟩ := bounded_connected_plane_complement_open_disk fo fc size outside
  let e : ℂ ≃ₜ F := Homeomorph.unitBall.trans disk.symm
  have sep {a : ℂ} (nz : a≠0) (ha : a∈L.lattice) : Disjoint F ((Homeomorph.addRight a) '' F) := by
    apply boundedPlaneFill_disjoint_translate bounded opened connected nz
    apply disjoint_left.mpr
    rintro _ overlap ⟨y,hy,rfl⟩
    have eq := injective overlap hy (periodTorusProjection_add_lattice L y a ha)
    change y+a=y at eq
    exact nz (add_left_cancel (show y+a=y+0 by simpa only [add_zero] using eq))
  have injF : InjOn (periodTorusProjection L) F := by
    intro x hx y hy eq
    by_contra diff
    have h := sep (sub_ne_zero.mpr (Ne.symm diff)) ((periodTorusProjection_eq_iff L x y).mp eq)
    exact disjoint_left.mp h hy ⟨x,hx,show x+(y-x)=y by abel⟩
  let P := F.domRestrict (periodTorusProjection L)
  have projection :=  (periodTorusProjection_isCoveringMap L).isLocalHomeomorph
  have ep : IsOpenEmbedding P := .of_continuous_injective_isOpenMap
    (projection.continuous.comp continuous_subtype_val)
    (fun x y eq => Subtype.ext (injF x.2 y.2 eq))
    (projection.isOpenMap.comp fo.isOpenEmbedding_subtypeVal.isOpenMap)
  refine ⟨P ∘ e,ep.comp e.isOpenEmbedding,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  let v : F := ⟨x,inc hx⟩
  exact ⟨e.symm v,congrArg P (e.apply_symm_apply v)⟩

/-- An arbitrary embedded closed disk on the torus lies in one open
plane chart. The construction only uses its compact connected lift and
the disjoint lattice translates; it also covers a nonsmooth boundary. -/
theorem embedded_torus_disk_in_plane_chart (L : PeriodPair)
    (u : C(closedBall (0:ℂ) 1,PeriodTorus L)) (emb : IsEmbedding u) :
    ∃ j : ℂ → PeriodTorus L, IsOpenEmbedding j ∧ range u⊆range j := by
  obtain ⟨f,V,lift,_,op,inside,sheet⟩ := embedded_torus_disk_has_injective_planar_neighborhood L u emb
  let K := range f
  have ck : IsCompact K := isCompact_range f.continuous
  obtain ⟨B,bound⟩ := ck.isBounded.exists_norm_le
  let r := B+1
  let T := V∩ball (0:ℂ) r
  have kt : K⊆T := fun z hz => ⟨inside hz,mem_ball_zero_iff.mpr (by dsimp only [r]; linarith [bound z hz])⟩
  let p := f (⟨0,mem_closedBall_self (x:=(0:ℂ)) zero_le_one⟩ : closedBall (0:ℂ) 1)
  have pk : p∈K := mem_range_self _
  let O := connectedComponentIn T p
  have co : IsConnected O := isConnected_connectedComponentIn_iff.mpr (kt pk)
  have ot : O⊆T := connectedComponentIn_subset _ _
  have opened : IsOpen O := (op.inter isOpen_ball).connectedComponentIn
  let _ : PreconnectedSpace (closedBall (0:ℂ) 1) := isPreconnected_iff_preconnectedSpace.mp (convex_closedBall (0:ℂ) 1).isPreconnected
  have ks : K⊆O := (isPreconnected_range f.continuous).subset_connectedComponentIn pk kt
  obtain ⟨j,ej,covers⟩ := filled_torus_lift_chart L opened co
    (isBounded_ball.subset (fun x hx => (ot hx).2)) (by
      intro x hx y hy eq
      let vx : V := ⟨x,(ot hx).1⟩
      let vy : V := ⟨y,(ot hy).1⟩
      have e : vx=vy := sheet.injective (show V.domRestrict (periodTorusProjection L) vx=V.domRestrict (periodTorusProjection L) vy from eq)
      exact congrArg Subtype.val e)
  refine ⟨j,ej,?_⟩
  rintro _ ⟨x,rfl⟩
  exact covers ⟨f x,ks (mem_range_self x),lift x⟩

/-- The punctured torus embeds in the complement of every topological
closed disk on it, without a planar Schönflies assumption. -/
theorem embedded_torus_disk_complement_has_open_handle (L : PeriodPair)
    (u : C(closedBall (0:ℂ) 1,PeriodTorus L)) (emb : IsEmbedding u) :
    ∃ f : PuncturedPeriodTorus L → {p : PeriodTorus L // p∉range u}, IsOpenEmbedding f := by
  let _ : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  obtain ⟨j,ej,inside⟩ := embedded_torus_disk_in_plane_chart L u emb
  obtain ⟨f,openf⟩ := punctured_surface_embeds_outside_compact_planar_chart j ej (range u) (isCompact_range u.continuous) inside
  let tr := Homeomorph.addRight (j 0)
  have move : tr 0=j 0 := zero_add _
  let S := {x : PeriodTorus L | x≠0}
  let T := {x : PeriodTorus L | x≠j 0}
  have eq : tr '' S=T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩ h
      exact hx (tr.injective (h.trans move.symm))
    · intro hy
      refine ⟨tr.symm y,?_,tr.apply_symm_apply y⟩
      intro h
      exact hy ((tr.apply_symm_apply y).symm.trans ((congrArg tr h).trans move))
  let puncture := (tr.isEmbedding.homeomorphImage S).trans (Homeomorph.setCongr eq)
  exact ⟨f ∘ puncture,openf.comp puncture.isOpenEmbedding⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.filled_torus_lift_chart
#print axioms TwoAxisHelicoid.embedded_torus_disk_in_plane_chart
#print axioms TwoAxisHelicoid.embedded_torus_disk_complement_has_open_handle
