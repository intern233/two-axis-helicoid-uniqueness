import TwoAxisHelicoid.InfinitePlanarIndex

namespace TwoAxisHelicoid
open Set Function
open scoped ContDiff

theorem compact_planar_translates_escape {K : Set (ℝ × ℝ)} (hK : IsCompact K) (R : ℝ) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ K, R < ‖p+(s,0)‖ := by
  obtain ⟨C,_hC,hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R+C+1,?_⟩
  intro s hs p hp
  have hpC : |p.1| ≤ C := (norm_fst_le p).trans (hbound p hp)
  have hn : p.1+s ≤ ‖p+(s,0)‖ :=
    (le_abs_self _).trans (norm_fst_le (p+(s,0)))
  have hlo := (abs_le.mp hpC).1
  linarith

theorem planarTranslate_tsupport_eventually_outside {v : ℝ × ℝ → ℝ}
    (hs : HasCompactSupport v) (R : ℝ) :
    ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ tsupport (planarTranslate v s), R < ‖p‖ := by
  obtain ⟨S,hS⟩ := compact_planar_translates_escape hs R
  refine ⟨S,?_⟩
  intro s hsS p hp
  rw [planarTranslate_tsupport] at hp
  simpa only [sub_add_cancel] using hS s hsS (p-(s,0)) hp

def HasInfiniteCompactPlanarIndexAtInfinity (W : ℝ × ℝ → ℝ) : Prop :=
  ∀ R : ℝ, ∀ n : ℕ, ∃ v : Fin n → ℝ × ℝ → ℝ,
    (∀ i, ContDiff ℝ ∞ (v i) ∧ HasCompactSupport (v i)) ∧
    (∀ i, ∀ p ∈ tsupport (v i), R < ‖p‖) ∧ LinearIndependent ℝ v ∧
    ∀ c : Fin n → ℝ, c ≠ 0 → planarQuadraticEnergy W (fun p => ∑ i, c i*v i p) < 0

theorem HasInfiniteCompactPlanarIndexAtInfinity.infinite_index {W : ℝ × ℝ → ℝ}
    (h : HasInfiniteCompactPlanarIndexAtInfinity W) : HasInfiniteCompactPlanarIndex W := by
  intro n
  obtain ⟨v,hv,_hf,hi,hq⟩ := h 0 n
  exact ⟨v,hv,hi,hq⟩

theorem infinite_planar_index_at_infinity_of_potential_limit
    {W : ℝ × ℝ → ℝ} {V : ℝ → ℝ} (hW : Continuous W) (hV : Continuous V)
    (hn : ∀ y, 0 ≤ V y) (hp : 0 < V 0)
    (hlimit : ∀ K : Set (ℝ × ℝ), IsCompact K → ∀ ε > 0, ∃ S : ℝ,
      ∀ s ≥ S, ∀ p ∈ K, |W (p+(s,0))-V p.2| ≤ ε) :
    HasInfiniteCompactPlanarIndexAtInfinity W := by
  obtain ⟨v,hv,hs,hq⟩ := exists_planar_smooth_compact_negative_direction hV hn hp
  have hQ : planarQuadraticEnergy (fun p => V p.2) v < 0 := by
    rwa [planarQuadraticEnergy_eq_schrodinger (hv.differentiable (by simp))]
  obtain ⟨S,hS⟩ := planar_negative_translates_eventually hW (hV.comp continuous_snd) hv hs hQ
    (hlimit (tsupport v) hs)
  intro R n
  obtain ⟨T,hT⟩ := planarTranslate_tsupport_eventually_outside hs R
  obtain ⟨s,hfar,hdis⟩ := finite_disjoint_far_translates hs (max S T) n
  let f : Fin n → ℝ × ℝ → ℝ := fun i => planarTranslate v (s i)
  have hf (i : Fin n) : ContDiff ℝ ∞ (f i) := planarTranslate_contDiff hv (s i)
  have hfs (i : Fin n) : HasCompactSupport (f i) := planarTranslate_hasCompactSupport hs (s i)
  have hfq (i : Fin n) : planarQuadraticEnergy W (f i) < 0 :=
    hS (s i) ((le_max_left _ _).trans (hfar i))
  refine ⟨f,fun i => ⟨hf i,hfs i⟩,?_,
    planar_negative_disjoint_family_independent hW hf hfs hdis hfq,?_⟩
  · intro i p hp
    exact hT (s i) ((le_max_right _ _).trans (hfar i)) p hp
  · intro c hc
    exact planarQuadraticEnergy_disjoint_sum_negative hW hf hfs hdis hfq hc

theorem planarQuadraticEnergy_eq_of_agree_on_support {W V v : ℝ × ℝ → ℝ}
    (h : ∀ p, v p ≠ 0 → W p = V p) : planarQuadraticEnergy W v = planarQuadraticEnergy V v := by
  unfold planarQuadraticEnergy
  congr 1
  funext p
  by_cases hp : v p = 0
  · simp [hp]
  · rw [h p hp]

theorem HasInfiniteCompactPlanarIndexAtInfinity.congr_outside {W V : ℝ × ℝ → ℝ}
    (h : HasInfiniteCompactPlanarIndexAtInfinity W) {B : ℝ}
    (he : ∀ p, B ≤ ‖p‖ → W p = V p) : HasInfiniteCompactPlanarIndexAtInfinity V := by
  intro R n
  obtain ⟨v,hv,hfar,hi,hq⟩ := h (max R B) n
  refine ⟨v,hv,fun i p hp => (le_max_left _ _).trans_lt (hfar i p hp),hi,?_⟩
  intro c hc
  have heq : planarQuadraticEnergy V (fun p => ∑ i, c i*v i p) =
      planarQuadraticEnergy W (fun p => ∑ i, c i*v i p) := by
    apply planarQuadraticEnergy_eq_of_agree_on_support
    intro p hp
    have hBp : B ≤ ‖p‖ := by
      by_contra hn
      have hz (i : Fin n) : v i p = 0 := by
        by_contra hnon
        have hh := (le_max_right R B).trans_lt (hfar i p (subset_closure hnon))
        exact hn hh.le
      exact hp (by simp [hz])
    exact (he p hBp).symm
  rw [heq]
  exact hq c hc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.infinite_planar_index_at_infinity_of_potential_limit
#print axioms TwoAxisHelicoid.HasInfiniteCompactPlanarIndexAtInfinity.congr_outside
