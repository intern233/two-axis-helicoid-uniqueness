import TwoAxisHelicoid.CircleLiftNeighborhood
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace TwoAxisHelicoid
open Set Metric

private theorem phase_lifts_on_disjoint_union {X ι : Type*} [TopologicalSpace X] [NormalSpace X]
    {φ : X → Circle} (t : Finset ι) (B : ι → Set X) (closed : ∀ i, IsClosed (B i))
    (disjoint : ∀ i j, i≠j → Disjoint (B i) (B j)) (lift : ∀ i, PhaseLiftsOn φ (B i)) :
    PhaseLiftsOn φ (⋃ i∈t,B i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert i t fresh ih =>
    rw [Finset.set_biUnion_insert]
    apply (lift i).disjoint_union ih (closed i) (isClosed_biUnion_finset fun j _ => closed j)
    refine Set.disjoint_left.mpr ?_
    intro x xi xu
    obtain ⟨j,jt,xj⟩ := mem_iUnion₂.mp xu
    exact Set.disjoint_left.mp (disjoint i j (fun e => fresh (e ▸ jt))) xi xj

/-- Color the equal-width height bands alternately. If both phases lift locally
over intervals of height, one phase has a lift on the union of the even closed
bands and the other one on the union of the odd closed bands. -/
theorem two_closed_sets_from_height_lifts {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {h : X → ℝ} (ch : Continuous h) (φ ψ : X → Circle)
    (localLifts : ∀ t : ℝ, ∃ O : Set ℝ, IsOpen O ∧ t∈O ∧
      PhaseLiftsOn φ (h ⁻¹' O) ∧ PhaseLiftsOn ψ (h ⁻¹' O)) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ (∀ x, x∈A ∨ x∈B) ∧ PhaseLiftsOn φ A ∧ PhaseLiftsOn ψ B := by
  classical
  choose O op own left right using localLifts
  obtain ⟨M,bound⟩ := isCompact_univ.exists_bound_of_continuousOn ch.continuousOn
  have bounded (x : X) : h x∈Icc (-M) M := abs_le.mp ((Real.norm_eq_abs _).symm ▸ bound x (mem_univ _))
  obtain ⟨δ,pos,cover⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a:=-M) (b:=M)) op
    (fun x _ => mem_iUnion.mpr ⟨x,own x⟩)
  let d := δ/2
  have dp : 0<d := half_pos pos
  let c := fun n : ℕ => -M+n*d
  have step (n : ℕ) : c (n+1)=c n+d := by simp [c,add_mul]; ring
  have inc : StrictMono c := strictMono_nat_of_lt_succ (fun n => by rw [step]; linarith)
  let band := fun n : ℕ => h ⁻¹' Icc (c n) (c (n+1))
  have cl (n : ℕ) : IsClosed (band n) := isClosed_Icc.preimage ch
  have lifts (n : ℕ) : PhaseLiftsOn φ (band n) ∧ PhaseLiftsOn ψ (band n) := by
    by_cases ne : (band n).Nonempty
    · obtain ⟨x,hx⟩ := ne
      obtain ⟨i,large⟩ := cover (h x) (bounded x)
      have sub : band n⊆h ⁻¹' O i := by
        intro y hy
        apply large
        change dist (h y) (h x)<δ
        rw [Real.dist_eq,abs_lt]
        have hx' : h x∈Icc (c n) (c n+d) := step n ▸ hx
        have hy' : h y∈Icc (c n) (c n+d) := step n ▸ hy
        dsimp [d] at hx' hy'
        constructor <;> linarith [hx'.1,hx'.2,hy'.1,hy'.2]
      exact ⟨(left i).mono sub,(right i).mono sub⟩
    · exact ⟨⟨0,fun x hx => (ne ⟨x,hx⟩).elim⟩,⟨0,fun x hx => (ne ⟨x,hx⟩).elim⟩⟩
  have ordered {i j : ℕ} (ij : i+1<j) : Disjoint (band i) (band j) :=
    Set.disjoint_left.mpr (fun _ hi hj => (inc ij).not_ge (hj.1.trans hi.2))
  have dis (o i j : ℕ) (ne : i≠j) : Disjoint (band (2*i+o)) (band (2*j+o)) := by
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact ordered (by omega)
    · exact (ordered (i:=2*j+o) (j:=2*i+o) (by omega)).symm
  obtain ⟨N,large⟩ := exists_nat_gt ((2*M)/d)
  have last : M≤c (N+1) := by
    have enough := (div_lt_iff₀ dp).mp large
    rw [step]; dsimp [c]
    linarith
  have between (n : ℕ) (x : ℝ) (start : c 0≤x) (stop : x≤c (n+1)) :
      ∃ k≤n, x∈Icc (c k) (c (k+1)) := by
    induction n with
    | zero => exact ⟨0,le_rfl,start,stop⟩
    | succ n ih =>
      by_cases before : x≤c (n+1)
      · obtain ⟨k,le,mem⟩ := ih before
        exact ⟨k,Nat.le_succ_of_le le,mem⟩
      · exact ⟨n+1,le_rfl,le_of_not_ge before,stop⟩
  let t := Finset.range (N+1)
  let U := fun o : ℕ => ⋃ i∈t, band (2*i+o)
  have closed (o : ℕ) : IsClosed (U o) := isClosed_biUnion_finset (fun i _ => cl _)
  refine ⟨U 0,U 1,closed 0,closed 1,?_,
    phase_lifts_on_disjoint_union t _ (fun i => cl _) (dis 0) (fun i => (lifts _).1),
    phase_lifts_on_disjoint_union t _ (fun i => cl _) (dis 1) (fun i => (lifts _).2)⟩
  intro x
  obtain ⟨k,le,hk⟩ := between N (h x) (by simpa [c] using (bounded x).1) ((bounded x).2.trans last)
  have kt : k/2∈t := Finset.mem_range.mpr (by omega)
  have parity : k=2*(k/2)+0 ∨ k=2*(k/2)+1 := by omega
  rcases parity with eq|eq
  · exact Or.inl (mem_iUnion₂.mpr ⟨k/2,kt,eq ▸ hk⟩)
  · exact Or.inr (mem_iUnion₂.mpr ⟨k/2,kt,eq ▸ hk⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.two_closed_sets_from_height_lifts
