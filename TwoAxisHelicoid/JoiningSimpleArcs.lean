import Mathlib.Topology.Subpath
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Function Topology
open scoped unitInterval

/-- Restricting an injective arc to two different parameters preserves
injectivity, in either orientation. -/
theorem injective_subpath {M : Type*} [TopologicalSpace M] {a b : M} {γ : Path a b}
    (inj : Injective γ) {s t : unitInterval} (st : s≠t) : Injective (γ.subpath s t) := by
  intro i j eq
  have h := congrArg Subtype.val (inj eq)
  change (1-(i:ℝ))*s+i*t=(1-(j:ℝ))*s+j*t at h
  apply Subtype.ext
  have prod : ((i:ℝ)-j)*((t:ℝ)-s)=0 := by linarith only [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_right (sub_ne_zero.mpr (fun e => st (Subtype.ext e.symm))))

/-- The only possible repeated value of two simple arcs meeting at
their endpoints is the common starting and finishing point. -/
theorem concatenated_arc_collisions {M : Type*} [TopologicalSpace M] {a b c : M}
    {f : Path a b} {g : Path b c} (fi : Injective f) (gi : Injective g)
    (cross : ∀ i j, f i=g j → (i=1 ∧ j=0) ∨ (i=0 ∧ j=1)) (x y : unitInterval)
    (eq : (f.trans g) x=(f.trans g) y) : x=y ∨ (x=0 ∧ y=1) ∨ (y=0 ∧ x=1) := by
  rw [Path.trans_apply,Path.trans_apply] at eq
  split_ifs at eq with hx hy hy
  · left
    have h := congrArg Subtype.val (fi eq)
    exact Subtype.ext (by dsimp at h; linarith)
  · rcases cross _ _ eq with ⟨_,z⟩|⟨z,o⟩
    · have h := congrArg Subtype.val z
      change 2*(y:ℝ)-1=0 at h
      exact (hy (by linarith)).elim
    · have h := congrArg Subtype.val z
      have h' := congrArg Subtype.val o
      change 2*(x:ℝ)=0 at h
      change 2*(y:ℝ)-1=1 at h'
      exact Or.inr (Or.inl ⟨Subtype.ext (by change (x:ℝ)=0; linarith),Subtype.ext (by change (y:ℝ)=1; linarith)⟩)
  · rcases cross _ _ eq.symm with ⟨_,z⟩|⟨z,o⟩
    · have h := congrArg Subtype.val z
      change 2*(x:ℝ)-1=0 at h
      exact (hx (by linarith)).elim
    · have h := congrArg Subtype.val z
      have h' := congrArg Subtype.val o
      change 2*(y:ℝ)=0 at h
      change 2*(x:ℝ)-1=1 at h'
      exact Or.inr (Or.inr ⟨Subtype.ext (by change (y:ℝ)=0; linarith),Subtype.ext (by change (x:ℝ)=1; linarith)⟩)
  · left
    have h := congrArg Subtype.val (gi eq)
    exact Subtype.ext (by dsimp at h; linarith)

def SimpleArcJoined {M : Type*} [TopologicalSpace M] (a b : M) : Prop :=
  a=b ∨ ∃ γ : Path a b, Injective γ

theorem SimpleArcJoined.symm {M : Type*} [TopologicalSpace M] {a b : M}
    (h : SimpleArcJoined a b) : SimpleArcJoined b a := by
  rcases h with e|⟨f,fi⟩
  · exact Or.inl e.symm
  · exact Or.inr ⟨f.symm,fi.comp unitInterval.symm_bijective.injective⟩

/-- The first hit of the second compact arc trims away all previous
intersections. This proves transitivity without assuming a general
arc-extraction theorem for arbitrary paths. -/
theorem SimpleArcJoined.trans {M : Type*} [TopologicalSpace M] [T2Space M] {a b c : M}
    (first : SimpleArcJoined a b) (second : SimpleArcJoined b c) : SimpleArcJoined a c := by
  classical
  rcases first with e|⟨f,fi⟩
  · exact e.symm ▸ second
  rcases second with e|⟨g,gi⟩
  · exact e ▸ (Or.inr ⟨f,fi⟩ : SimpleArcJoined a b)
  by_cases ac : a=c
  · exact Or.inl ac
  let T := f ⁻¹' range g
  have closed : IsClosed T := (isCompact_range g.continuous).isClosed.preimage f.continuous
  have one : (1:unitInterval)∈T := ⟨0,g.source.trans f.target.symm⟩
  obtain ⟨i,hi,firstHit⟩ := closed.isCompact.exists_isMinOn ⟨1,one⟩ continuous_id.continuousOn
  obtain ⟨j,join⟩ := hi
  let F := (f.subpath 0 i).cast f.source.symm (rfl : f i=f i)
  let G := (g.subpath j 1).cast join.symm g.target.symm
  by_cases iz : i=0
  · have ja : a=g j := f.source.symm.trans (iz ▸ join.symm)
    have ne : j≠1 := fun eq => ac (ja.trans ((congrArg g eq).trans g.target))
    exact Or.inr ⟨(g.subpath j 1).cast ja g.target.symm,injective_subpath gi ne⟩
  have fInj : Injective F := injective_subpath fi (Ne.symm iz)
  by_cases endp : j=1
  · have fc : c=f i := g.target.symm.trans ((congrArg g endp.symm).trans join)
    exact Or.inr ⟨F.cast rfl fc,fInj⟩
  have gInj : Injective G := injective_subpath gi endp
  have cross (u v : unitInterval) (eq : F u=G v) : u=1 ∧ v=0 := by
    let k := Icc.convexComb (0:unitInterval) i u
    have mem : k∈T := ⟨Icc.convexComb j 1 v,eq.symm⟩
    have low : (0 : unitInterval) ≤ i := i.2.1
    have same : k=i := (Icc.convexComb_le low u).antisymm (firstHit mem)
    have tip : F u=f i := congrArg f same
    exact ⟨fInj (tip.trans F.target.symm),gInj (eq.symm.trans (tip.trans G.source.symm))⟩
  refine Or.inr ⟨F.trans G,?_⟩
  intro x y xy
  rcases concatenated_arc_collisions fInj gInj (fun u v eq => Or.inl (cross u v eq)) x y xy with h|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact h
  · exact (ac ((F.trans G).source.symm.trans (xy.trans (F.trans G).target))).elim
  · exact (ac ((F.trans G).source.symm.trans (xy.symm.trans (F.trans G).target))).elim

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.injective_subpath
#print axioms TwoAxisHelicoid.concatenated_arc_collisions
#print axioms TwoAxisHelicoid.SimpleArcJoined.trans
