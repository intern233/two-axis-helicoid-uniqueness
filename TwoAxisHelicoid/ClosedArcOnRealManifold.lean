import TwoAxisHelicoid.ArcsInRealManifolds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle

namespace TwoAxisHelicoid
open Set Function Topology Metric
open scoped Topology unitInterval

/-- An embedded closed path exhausts a connected real one-manifold:
the real parametrization is locally injective and its image is open,
while the circle parameter gives compactness. -/
theorem real_manifold_circle_of_simple_loop {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] [ChartedSpace ℝ M] {p : M} (γ : Path p p)
    (hit : ∀ x y : unitInterval, γ x=γ y → x=y ∨ (x=0 ∧ y=1) ∨ (y=0 ∧ x=1)) :
    Nonempty (M ≃ₜ sphere (0:ℂ) 1) := by
  let C := AddCircle (1:ℝ)
  let π : ℝ → C := (↑)
  let F := AddCircle.liftIco (1:ℝ) 0 γ.extend
  have cf : Continuous F := AddCircle.liftIco_zero_continuous (γ.extend_zero.trans γ.extend_one.symm) γ.continuous_extend.continuousOn
  let param := fun z : C => AddCircle.equivIco (1:ℝ) 0 z
  let u := fun z : C => (⟨(param z).1,(param z).2.1,by simpa using (param z).2.2.le⟩ : unitInterval)
  have val (z : C) : F z=γ (u z) := by
    change γ.extend (param z).1 = γ (u z)
    exact γ.extend_extends' (u z)
  have last (z : C) : u z≠1 := by
    intro eq
    have n : (u z:ℝ)=1 := congrArg Subtype.val eq
    change (param z).1 = 1 at n
    have lo : (param z).1<1 := by simpa using (param z).2.2
    exact lo.ne n
  have inj : Injective F := by
    intro x y eq
    rcases hit (u x) (u y) ((val x).symm.trans (eq.trans (val y))) with h|⟨_,h⟩|⟨_,h⟩
    · have vals := congrArg (fun t : unitInterval => t.1) h
      apply (AddCircle.equivIco (1:ℝ) 0).injective
      exact Subtype.ext vals
    · exact (last y h).elim
    · exact (last x h).elim
  have co := AddCircle.isCoveringMap_coe (1:ℝ)
  have loc : IsLocallyInjective (F ∘ π) := by
    intro t
    obtain ⟨U,ou,ut,i⟩ := co.isLocalHomeomorph.isLocallyInjective t
    exact ⟨U,ou,ut,fun _ hx _ hy eq => i hx hy (inj eq)⟩
  have op := real_manifold_locally_injective_curve_open (cf.comp co.continuous) loc
  have sur : Surjective π := Quotient.mk_surjective
  rw [range_comp,sur.range_eq,image_univ] at op
  have onto := IsClopen.eq_univ ⟨(isCompact_range cf).isClosed,op⟩ (range_nonempty F)
  have emb := cf.isClosedEmbedding inj
  let H := emb.isEmbedding.toHomeomorphOfSurjective (range_eq_univ.mp onto)
  exact ⟨H.symm.trans (AddCircle.homeomorphCircle (one_ne_zero : (1:ℝ)≠0))⟩

/-- A simple arc in a punctured real manifold joining the opposite
sides of a coordinate yields a simple closed curve. We locate the
last and first contacts with the arc on the two halves of the coordinate. -/
theorem simple_closed_loop_from_bypass {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] [ChartedSpace ℝ M] (j : ℝ → M) (ej : IsOpenEmbedding j)
    (γ : Path (j (-1)) (j 1)) (inj : Injective γ) (avoid : j 0∉range γ) :
    Nonempty (M ≃ₜ sphere (0:ℂ) 1) := by
  let T := j ⁻¹' range γ
  have closed : IsClosed T := (isCompact_range γ.continuous).isClosed.preimage ej.continuous
  have left : (-1:ℝ)∈T := ⟨0,γ.source⟩
  have right : (1:ℝ)∈T := ⟨1,γ.target⟩
  obtain ⟨a,⟨ha,ua⟩,maximum⟩ := (isCompact_Icc.inter_right closed).exists_isMaxOn
    (show (Icc (-1:ℝ) 0 ∩ T).Nonempty from ⟨-1,⟨le_rfl,by norm_num⟩,left⟩) continuous_id.continuousOn
  obtain ⟨b,⟨hb,ub⟩,minimum⟩ := (isCompact_Icc.inter_right closed).exists_isMinOn
    (show (Icc (0:ℝ) 1 ∩ T).Nonempty from ⟨1,⟨zero_le_one,le_rfl⟩,right⟩) continuous_id.continuousOn
  have neg : a<0 := lt_of_le_of_ne ha.2 (fun eq => avoid (eq ▸ ua))
  have pos : 0<b := lt_of_le_of_ne hb.1 (fun eq => avoid (eq.symm ▸ ub))
  have ab := neg.trans pos
  have gap {x : ℝ} (lo : a<x) (hi : x<b) : x∉T := by
    intro xt
    by_cases s : x≤0
    · exact lo.not_ge (maximum (show x∈Icc (-1:ℝ) 0 ∩ T from ⟨⟨ha.1.trans lo.le,s⟩,xt⟩))
    · exact hi.not_ge (minimum (show x∈Icc (0:ℝ) 1 ∩ T from ⟨⟨(lt_of_not_ge s).le,hi.le.trans hb.2⟩,xt⟩))
  obtain ⟨i,ai⟩ := ua
  obtain ⟨k,bk⟩ := ub
  have ki : k≠i := fun eq => ab.ne (ej.injective (ai.symm.trans ((congrArg γ eq.symm).trans bk)))
  let f := (Path.segment a b).map ej.continuous
  let g := (γ.subpath k i).cast bk.symm ai.symm
  have fi : Injective f := ej.injective.comp (Path.segment_injective_of_ne ab.ne)
  have gi : Injective g := injective_subpath inj ki
  have cross (u v : unitInterval) (eq : f u=g v) : (u=1 ∧ v=0) ∨ (u=0 ∧ v=1) := by
    let x := Path.segment a b u
    have xt : x∈T := ⟨Icc.convexComb k i v,eq.symm⟩
    have bounds : x∈Icc a b := by
      have h := mem_range_self (f := Path.segment a b) u
      rw [Path.range_segment,segment_eq_uIcc,uIcc_of_le ab.le] at h
      exact h
    rcases bounds.1.eq_or_lt with h|lo
    · have tip : f u=j a := congrArg j h.symm
      exact Or.inr ⟨fi (tip.trans f.source.symm),gi (eq.symm.trans (tip.trans g.target.symm))⟩
    rcases bounds.2.eq_or_lt with h|hi
    · have tip : f u=j b := congrArg j h
      exact Or.inl ⟨fi (tip.trans f.target.symm),gi (eq.symm.trans (tip.trans g.source.symm))⟩
    exact (gap lo hi xt).elim
  exact real_manifold_circle_of_simple_loop (f.trans g) (concatenated_arc_collisions fi gi cross)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.real_manifold_circle_of_simple_loop
#print axioms TwoAxisHelicoid.simple_closed_loop_from_bypass
