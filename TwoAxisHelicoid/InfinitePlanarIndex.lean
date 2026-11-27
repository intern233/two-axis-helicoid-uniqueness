import TwoAxisHelicoid.PlanarDisjointEnergy
import TwoAxisHelicoid.PlanarTranslation
import TwoAxisHelicoid.PlanarNegativeDirection

namespace TwoAxisHelicoid
open Set Function
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem finite_disjoint_far_translates {v : ℝ × ℝ → ℝ} (hs : HasCompactSupport v)
    (S : ℝ) (n : ℕ) :
    ∃ s : Fin n → ℝ, (∀ i, S ≤ s i) ∧
      Pairwise (fun i j => Disjoint (tsupport (planarTranslate v (s i)))
        (tsupport (planarTranslate v (s j)))) := by
  obtain ⟨R,hR,hbound⟩ := hs.isBounded.exists_pos_norm_le
  let s : Fin n → ℝ := fun i => S+(i.val : ℝ)*(2*R+1)
  have hstep (i j : Fin n) (hij : i < j) : 2*R+1 ≤ s j-s i := by
    have hi : (i.val : ℝ)+1 ≤ (j.val : ℝ) := by
      exact_mod_cast (show i.val+1 ≤ j.val from Nat.add_one_le_iff.mpr hij)
    have hmul := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ (j.val : ℝ)-(i.val : ℝ) by linarith)
      (show 0 ≤ 2*R+1 by linarith)
    dsimp [s]
    nlinarith
  refine ⟨s,?_,?_⟩
  · intro i
    dsimp [s]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    rw [planarTranslate_tsupport] at hpi hpj
    have hi : |p.1-s i| ≤ R := by
      simpa only [Prod.fst_sub,Real.norm_eq_abs] using
        (norm_fst_le (p-(s i,0))).trans (hbound _ hpi)
    have hj : |p.1-s j| ≤ R := by
      simpa only [Prod.fst_sub,Real.norm_eq_abs] using
        (norm_fst_le (p-(s j,0))).trans (hbound _ hpj)
    obtain ⟨hi₁,hi₂⟩ := abs_le.mp hi
    obtain ⟨hj₁,hj₂⟩ := abs_le.mp hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hh := hstep i j hij
      linarith
    · have hh := hstep j i hji
      linarith

/-- Arbitrarily large negative subspaces, expressed by linearly independent
smooth compact tests and strict negativity of every nonzero combination. -/
def HasInfiniteCompactPlanarIndex (W : ℝ × ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ v : Fin n → ℝ × ℝ → ℝ,
    (∀ i, ContDiff ℝ ∞ (v i) ∧ HasCompactSupport (v i)) ∧ LinearIndependent ℝ v ∧
    ∀ c : Fin n → ℝ, c ≠ 0 → planarQuadraticEnergy W (fun p => ∑ i, c i*v i p) < 0

/-- The functional-analytic infinite-index argument for potentials whose
horizontal translates approach the helicoid potential uniformly on compact
sets. Identifying this planar form with a surface's geometric second
variation is a separate geometric theorem. -/
theorem infinite_planar_index_of_potential_limit {W : ℝ × ℝ → ℝ} {V : ℝ → ℝ}
    (hW : Continuous W) (hV : Continuous V) (hn : ∀ y, 0 ≤ V y) (hp : 0 < V 0)
    (hlimit : ∀ K : Set (ℝ × ℝ), IsCompact K → ∀ ε > 0, ∃ S : ℝ,
      ∀ s ≥ S, ∀ p ∈ K, |W (p+(s,0))-V p.2| ≤ ε) :
    HasInfiniteCompactPlanarIndex W := by
  obtain ⟨v,hv,hs,hq⟩ := exists_planar_smooth_compact_negative_direction hV hn hp
  have hQ : planarQuadraticEnergy (fun p => V p.2) v < 0 := by
    rwa [planarQuadraticEnergy_eq_schrodinger (hv.differentiable (by simp))]
  obtain ⟨S,hS⟩ := planar_negative_translates_eventually hW (hV.comp continuous_snd) hv hs hQ
    (hlimit (tsupport v) hs)
  intro n
  obtain ⟨s,hfar,hdis⟩ := finite_disjoint_far_translates hs S n
  let f : Fin n → ℝ × ℝ → ℝ := fun i => planarTranslate v (s i)
  have hf (i : Fin n) : ContDiff ℝ ∞ (f i) := planarTranslate_contDiff hv (s i)
  have hfs (i : Fin n) : HasCompactSupport (f i) := planarTranslate_hasCompactSupport hs (s i)
  have hfq (i : Fin n) : planarQuadraticEnergy W (f i) < 0 := hS (s i) (hfar i)
  refine ⟨f,fun i => ⟨hf i,hfs i⟩,
    planar_negative_disjoint_family_independent hW hf hfs hdis hfq,?_⟩
  intro c hc
  exact planarQuadraticEnergy_disjoint_sum_negative hW hf hfs hdis hfq hc

theorem infinite_planar_index_of_helicoid_limit {W : ℝ × ℝ → ℝ} (hW : Continuous W)
    (hlimit : ∀ K : Set (ℝ × ℝ), IsCompact K → ∀ ε > 0, ∃ S : ℝ,
      ∀ s ≥ S, ∀ p ∈ K, |W (p+(s,0))-2*helicoidGroundState p.2^2| ≤ ε) :
    HasInfiniteCompactPlanarIndex W := by
  apply infinite_planar_index_of_potential_limit (V := fun y => 2*helicoidGroundState y^2) hW _ _ _ hlimit
  · unfold helicoidGroundState
    fun_prop (disch := intros; positivity)
  · intro y; positivity
  · norm_num [helicoidGroundState]

theorem infinite_planar_index_of_scaled_helicoid_limit {W : ℝ × ℝ → ℝ} (hW : Continuous W)
    {α : ℝ} (hα : α ≠ 0)
    (hlimit : ∀ K : Set (ℝ × ℝ), IsCompact K → ∀ ε > 0, ∃ S : ℝ,
      ∀ s ≥ S, ∀ p ∈ K, |W (p+(s,0))-2*α^2*helicoidGroundState (α*p.2)^2| ≤ ε) :
    HasInfiniteCompactPlanarIndex W := by
  apply infinite_planar_index_of_potential_limit (V := fun y => 2*α^2*helicoidGroundState (α*y)^2) hW _ _ _ hlimit
  · unfold helicoidGroundState
    fun_prop (disch := intros; positivity)
  · intro y; positivity
  · have hp := sq_pos_of_ne_zero hα
    norm_num [helicoidGroundState]
    nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.finite_disjoint_far_translates
#print axioms TwoAxisHelicoid.infinite_planar_index_of_helicoid_limit
