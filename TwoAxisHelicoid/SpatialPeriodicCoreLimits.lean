import TwoAxisHelicoid.SpatialCoreSheetCharts

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- A periodic spatial limit supplies approximating charts on any fixed
translate of a bounded-height generating core. The translation step is
arbitrary. Both charts are selected on one common approximating surface. -/
theorem periodic_spatial_charts_give_two_core_patches (W : ℕ → PitchNormalizedBasicImmersion)
    (hW : ∀ n, W n ∈ embeddedPitchFamily) {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (v : C.carrier → ℝ) {d : ℝ} (hd : 0 < d) (bounded : BddAbove (range (fun q => |v q|)))
    (charts : ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, ∃ G : SpatialCoreSheetCharts C (W n),
      ∀ q : G.patch, |(W n).torusPosition q.1 2-(v (G.base ((W n).torusPosition q.1))+(k:ℝ)*d)| < ε) :
    ∃ n, HasTwoPeriodicCorePatches (W n) := by
  obtain ⟨B,hB⟩ := bounded
  obtain ⟨k,hk⟩ := exists_nat_gt (4*(max B 0+1)/d)
  have hk' := (div_lt_iff₀ hd).mp hk
  let h := (k:ℝ)*d/4
  have hh : 0 < h := by dsimp [h]; linarith [le_max_right B 0]
  have bigger : B < h := by dsimp [h]; linarith [le_max_left B 0]
  have hfour : 4*h = (k:ℝ)*d := by dsimp [h]; ring
  obtain ⟨n,⟨G,hG⟩,H,hH⟩ := ((charts 0 h hh).and (charts k h hh)).exists
  refine ⟨n,A,C,h,v,G.toNormalCorePatch (hW n),H.toNormalCorePatch (hW n),hh,
    fun q => abs_lt.mp ((hB (mem_range_self q)).trans_lt bigger),?_,?_⟩
  · intro q
    change |(W n).torusPosition q.1 2-v (G.base ((W n).torusPosition q.1))| < h
    simpa only [Nat.cast_zero,zero_mul,add_zero] using hG q
  · intro q
    rw [hfour]
    exact hH q

/-- A periodic marked limit with these local charts is impossible for
embedded once-punctured tori, regardless of its period or multiplicity. -/
theorem exclude_periodic_spatial_chart_limit (W : ℕ → PitchNormalizedBasicImmersion)
    (hW : ∀ n, W n ∈ embeddedPitchFamily) {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (v : C.carrier → ℝ) {d : ℝ} (hd : 0 < d) (bounded : BddAbove (range (fun q => |v q|))) :
    ¬ (∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, ∃ G : SpatialCoreSheetCharts C (W n),
      ∀ q : G.patch, |(W n).torusPosition q.1 2-(v (G.base ((W n).torusPosition q.1))+(k:ℝ)*d)| < ε) := by
  intro charts
  obtain ⟨n,hn⟩ := periodic_spatial_charts_give_two_core_patches W hW C v hd bounded charts
  exact excluded_periodic_core_patches _ hn

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exclude_periodic_spatial_chart_limit
