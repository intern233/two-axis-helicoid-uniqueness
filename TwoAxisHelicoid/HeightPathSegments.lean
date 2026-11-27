import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousOn

namespace TwoAxisHelicoid
open Set
open scoped unitInterval

/-- A height deformation on one closed time segment preserves the
given path at shift zero and the prescribed two moving endpoints.
The positive shift radius is uniform along the whole segment. -/
def HeightPathDeformationOn {M : Type*} [TopologicalSpace M] (h : M → ℝ) (v : ℝ → ℝ)
    (γ : I → M) (P : I → ℝ → M) (l r : I) : Prop :=
  ∃ d : ℝ, 0<d ∧ ∃ F : ℝ×I → M, ContinuousOn F (Icc (-d) d ×ˢ Icc l r) ∧
    (∀ t∈Icc l r, F (0,t)=γ t) ∧ ∀ s∈Icc (-d) d,
      (∀ t∈Icc l r, h (F (s,t))=v s) ∧ F (s,l)=P l s ∧ F (s,r)=P r s

/-- Two deformations agree along their common moving vertex and
therefore join to a genuine jointly continuous deformation. -/
theorem HeightPathDeformationOn.join {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} {v : ℝ → ℝ} {γ : I → M} {P : I → ℝ → M} {l m r : I}
    (lm : l≤m) (mr : m≤r) (left : HeightPathDeformationOn h v γ P l m)
    (right : HeightPathDeformationOn h v γ P m r) : HeightPathDeformationOn h v γ P l r := by
  obtain ⟨a,ap,A,ca,a0,al⟩ := left
  obtain ⟨b,bp,B,cb,b0,bl⟩ := right
  let d := min a b
  let U := Icc (-d) d
  let L := U ×ˢ Icc l m
  let R := U ×ˢ Icc m r
  let F := fun q : ℝ×I => if q.2≤m then A q else B q
  have dp : 0<d := lt_min ap bp
  have u0 : (0:ℝ)∈U := ⟨neg_nonpos.mpr dp.le,dp.le⟩
  have ua : U⊆Icc (-a) a := Icc_subset_Icc (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have ub : U⊆Icc (-b) b := Icc_subset_Icc (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have la : EqOn F A L := fun q hq => ite_eq_left hq.2.2
  have rb : EqOn F B R := by
    intro q hq
    by_cases old : q.2≤m
    · have t := le_antisymm old hq.2.1
      change (if q.2≤m then A q else B q)=B q
      rw [ite_eq_left old]
      obtain ⟨s,t'⟩ := q
      change t'=m at t
      subst t'
      exact (al s (ua hq.1)).2.2.trans (bl s (ub hq.1)).2.1.symm
    · exact ite_eq_right old
  have cL : ContinuousOn F L := (ca.mono (fun _ p => ⟨ua p.1,p.2⟩)).congr la
  have cR : ContinuousOn F R := (cb.mono (fun _ p => ⟨ub p.1,p.2⟩)).congr rb
  have lr : L∪R=U ×ˢ Icc l r := by
    ext q
    constructor
    · rintro (s|s)
      · exact ⟨s.1,s.2.1,s.2.2.trans mr⟩
      · exact ⟨s.1,lm.trans s.2.1,s.2.2⟩
    · rintro ⟨s,t⟩
      exact (le_total q.2 m).elim (fun p => Or.inl ⟨s,t.1,p⟩) (fun p => Or.inr ⟨s,p,t.2⟩)
  have continuous := cL.union_of_isClosed cR (isClosed_Icc.prod isClosed_Icc) (isClosed_Icc.prod isClosed_Icc)
  refine ⟨d,dp,F,lr ▸ continuous,?_,?_⟩
  · intro t ht
    rcases le_total t m with h|h
    · exact (la (show (0,t)∈L from ⟨u0,ht.1,h⟩)).trans (a0 t ⟨ht.1,h⟩)
    · exact (rb (show (0,t)∈R from ⟨u0,h,ht.2⟩)).trans (b0 t ⟨h,ht.2⟩)
  · intro s hs
    have leftData := al s (ua hs)
    have rightData := bl s (ub hs)
    refine ⟨?_,(la (show (s,l)∈L from ⟨hs,le_rfl,lm⟩)).trans leftData.2.1,
      (rb (show (s,r)∈R from ⟨hs,mr,le_rfl⟩)).trans rightData.2.2⟩
    intro t ht
    rcases le_total t m with h|h
    · exact (congrArg _ (la (show (s,t)∈L from ⟨hs,ht.1,h⟩))).trans (leftData.1 t ⟨ht.1,h⟩)
    · exact (congrArg _ (rb (show (s,t)∈R from ⟨hs,h,ht.2⟩))).trans (rightData.1 t ⟨h,ht.2⟩)

/-- A finite subdivision with shared endpoint sections gives uniform
height transport of the entire compact path. -/
theorem height_path_deformation_of_subdivision {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} {v : ℝ → ℝ} {γ : I → M} {P : I → ℝ → M} {N : ℕ} (cut : ℕ → I)
    (first : cut 0=0) (last : cut N=1) (ordered : Monotone cut)
    (segments : ∀ n<N, HeightPathDeformationOn h v γ P (cut n) (cut (n+1))) :
    HeightPathDeformationOn h v γ P 0 1 := by
  have initialSegments (n : ℕ) (hn : n<N) : HeightPathDeformationOn h v γ P (cut 0) (cut (n+1)) := by
    induction n with
    | zero => exact segments 0 hn
    | succ n ih =>
      exact HeightPathDeformationOn.join (ordered (Nat.zero_le _)) (ordered (Nat.le_succ _))
        (ih (Nat.lt_trans (Nat.lt_succ_self n) hn)) (segments (n+1) hn)
  cases N with
  | zero => exact (zero_ne_one (first.symm.trans last)).elim
  | succ n => simpa only [first,last] using initialSegments n (Nat.lt_succ_self n)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HeightPathDeformationOn.join
#print axioms TwoAxisHelicoid.height_path_deformation_of_subdivision

