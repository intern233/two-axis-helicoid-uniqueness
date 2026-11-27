import TwoAxisHelicoid.DisjointTorusCoreObstruction
import TwoAxisHelicoid.PuncturedTorusNoScrewPeriod

namespace TwoAxisHelicoid
open Set Topology

/-- A physical screw symmetry with nonzero vertical displacement produces arbitrarily
many compactly carried copies of the same genus-one core. Even the compact sets
carrying distinct copies are separated by a vertical distance greater than one. -/
theorem screw_period_repeats_compact_core {M : Type*} [TopologicalSpace M]
    (X : M → Fin 3 → ℝ) (emb : IsEmbedding X)
    (S : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) {d : ℝ} (step : d≠0)
    (moves : ∀ v, S v 2=v 2+d) (symmetry : S '' range X=range X)
    {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (f : C.carrier → M) (hf : IsOpenEmbedding f)
    (K : Set M) (compact : IsCompact K) (carried : range f ⊆ K) :
    ∃ F : ℕ → C.carrier → M, ∃ L : ℕ → Set M,
      (∀ i, IsOpenEmbedding (F i) ∧ IsCompact (L i) ∧ range (F i) ⊆ L i) ∧
      (∀ i j : ℕ, i<j → ∀ x∈L i, ∀ y∈L j, 1 < |X y 2-X x 2|) := by
  let σ := (S.isEmbedding.homeomorphImage (range X)).trans (Homeomorph.setCongr symmetry)
  let e := (emb.toHomeomorph.trans σ).trans emb.toHomeomorph.symm
  let h (q : M) := X q 2
  have shift (q : M) : h (e q)=h q+d := by
    have atX : X (e q)=S (X q) := congrArg Subtype.val (emb.toHomeomorph.apply_symm_apply (σ (emb.toHomeomorph q)))
    exact (congrFun atX 2).trans (moves (X q))
  let E : ℕ → M ≃ₜ M := Nat.rec (Homeomorph.refl _) (fun _ g => g.trans e)
  have iterate (n : ℕ) (q : M) : h (E n q)=h q+(n:ℝ)*d := by
    induction n with
    | zero => simp [E]
    | succ n ih =>
      change h (e (E n q))=_
      rw [shift,ih,Nat.cast_succ]
      ring
  have hc : Continuous h := (continuous_apply 2).comp emb.continuous
  obtain ⟨b,hb⟩ := compact.bddAbove_image hc.abs.continuousOn
  obtain ⟨N,hn⟩ := exists_nat_gt ((2*b+1)/|d|)
  have large := (div_lt_iff₀ (abs_pos.mpr step)).mp hn
  let T (i : ℕ) := E (N*i)
  let F (i : ℕ) := T i ∘ f
  let L (i : ℕ) := T i '' K
  refine ⟨F,L,fun i => ⟨(T i).isOpenEmbedding.comp hf,compact.image (T i).continuous,?_⟩,?_⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨f x,carried (mem_range_self x),rfl⟩
  · intro i j ij x hx y hy
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    have one : (1:ℝ)≤(j:ℝ)-(i:ℝ) := by
      have t : ((i+1:ℕ):ℝ)≤(j:ℝ) := by exact_mod_cast Nat.succ_le_of_lt ij
      push_cast at t
      linarith
    have pos : 0≤(j:ℝ)-(i:ℝ) := zero_le_one.trans one
    have weight := mul_le_mul_of_nonneg_right one (mul_nonneg (Nat.cast_nonneg N) (abs_nonneg d))
    rw [one_mul] at weight
    have eq : ((j:ℝ)-(i:ℝ))*(N:ℝ)*d=(h (T j v)-h (T i u))+(h u-h v) := by
      dsimp only [T]
      rw [iterate,iterate,Nat.cast_mul,Nat.cast_mul]
      ring
    have triangle := abs_add_le (h (T j v)-h (T i u)) (h u-h v)
    rw [←eq,abs_mul,abs_mul,abs_of_nonneg pos,abs_of_nonneg (Nat.cast_nonneg N),mul_assoc] at triangle
    have bu := hb (mem_image_of_mem _ hu)
    have bv := hb (mem_image_of_mem _ hv)
    change 1 < |h (T j v)-h (T i u)|
    linarith [abs_sub (h u) (h v)]

/-- Such a periodic surface cannot be the local single-sheeted limit on
compact sets of open pieces of marked tori. Only one neighbourhood
and the same comparison embedding for both handles are needed. -/
theorem screw_periodic_core_excludes_local_torus_embeddings {M : Type*} [TopologicalSpace M]
    (X : M → Fin 3 → ℝ) (emb : IsEmbedding X)
    (S : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) {d : ℝ} (step : d≠0)
    (moves : ∀ v, S v 2=v 2+d) (symmetry : S '' range X=range X)
    {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (f : C.carrier → M) (hf : IsOpenEmbedding f) (K : Set M)
    (compact : IsCompact K) (carried : range f ⊆ K) :
    ¬ (∀ B : Set M, IsCompact B → ∃ U : Set M, IsOpen U ∧ B⊆U ∧
      ∃ (T : PeriodPair) (j : U → PeriodTorus T), IsOpenEmbedding j) := by
  intro charts
  obtain ⟨F,L,atCore,separated⟩ := screw_period_repeats_compact_core X emb S step moves symmetry C f hf K compact carried
  obtain ⟨U,uo,cover,T,j,hj⟩ := charts (L 0 ∪ L 1) ((atCore 0).2.1.union (atCore 1).2.1)
  have inU (n : ℕ) (sub : L n⊆U) (q : C.carrier) : F n q∈U := sub ((atCore n).2.2 (mem_range_self q))
  let a (q : C.carrier) : U := ⟨F 0 q,inU 0 (subset_union_left.trans cover) q⟩
  let b (q : C.carrier) : U := ⟨F 1 q,inU 1 (subset_union_right.trans cover) q⟩
  have ha : IsOpenEmbedding a := (IsOpenEmbedding.of_comp_iff a uo.isOpenEmbedding_subtypeVal).mp (atCore 0).1
  have hb : IsOpenEmbedding b := (IsOpenEmbedding.of_comp_iff b uo.isOpenEmbedding_subtypeVal).mp (atCore 1).1
  apply disjoint_genus_one_cores_impossible C C (j ∘ a) (j ∘ b) (hj.comp ha) (hj.comp hb)
  apply Set.disjoint_left.mpr
  rintro _ ⟨p,rfl⟩ ⟨q,he⟩
  have same : F 1 q=F 0 p := congrArg Subtype.val (hj.injective he)
  have gap := separated 0 1 (by decide) _ ((atCore 0).2.2 (mem_range_self p)) _ ((atCore 1).2.2 (mem_range_self q))
  rw [same,sub_self,abs_zero] at gap
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.screw_period_repeats_compact_core
#print axioms TwoAxisHelicoid.screw_periodic_core_excludes_local_torus_embeddings
