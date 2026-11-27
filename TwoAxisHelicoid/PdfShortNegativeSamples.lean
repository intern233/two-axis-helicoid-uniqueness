import TwoAxisHelicoid.PdfFactoredPeriodicSamples
import TwoAxisHelicoid.PdfShortNegativeSampleError

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

theorem factored_negative_12_samples (M : ℕ) {t a : ℝ} {p : PrimalThetaParameters} (ps : p.Sound t a)
    {f : Fin 6 → FactoredFrequency} (fs : ∀ n : Fin 6, (f n).Sound t a n)
    {node : Fin 12 → Fin 6 → CGrid}
    (ns : ∀ (k : Fin 12) (n : Fin 6), (node k n).Contains (wavePhase n (-1+(k:ℝ)/12)))
    (ht : 9/10≤t) (hu : t≤7/5)
    (edge : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 →
      ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤(M:ℝ))
    (l u : ℕ → ℚ) (lo hi : ℚ)
    (good : ∀ k : Fin 12, containedInReported (sampledFactoredPrimal p f (node k)).re (l k) (u k)=true)
    (small : lo≤(∑ k∈Finset.range 12,l k)/12-(2*(M:ℚ)/(1000000-1)) ∧ (∑ k∈Finset.range 12,u k)/12+(2*(M:ℚ)/(1000000-1))≤hi) :
    (lo:ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(hi:ℝ) := by
  have hj (k : Fin 12) (j : Fin 5) := factored_sample_jets fs (ns k) (by linarith) hu j
  have bounds (k : Fin 12) := containedInReported_sound
    (primalValueOfJets_sound ps (fun j => (hj k j).1) (fun j => (hj k j).2)).1 (good k)
  let v := fun k : ℕ => (thetaA t a (((-1+(k:ℝ)/12:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re
  have low : (∑ k∈Finset.range 12,(l k:ℝ))≤∑ k∈Finset.range 12,v k :=
    Finset.sum_le_sum (fun k hk => (bounds ⟨k,Finset.mem_range.mp hk⟩).1)
  have high : (∑ k∈Finset.range 12,v k)≤∑ k∈Finset.range 12,(u k:ℝ) :=
    Finset.sum_le_sum (fun k hk => (bounds ⟨k,Finset.mem_range.mp hk⟩).2)
  have L := (Rat.cast_le (K:=ℝ)).mpr small.1
  have U := (Rat.cast_le (K:=ℝ)).mpr small.2
  push_cast at L U
  obtain ⟨left,right⟩ := abs_le.mp (negative_short_node_error (N:=12) (D:=1000000) (by decide) (by decide) negative_rate_twelve ht edge)
  change _* (∑ k∈Finset.range 12,v k) - _≤_ at right
  change _≤_* (∑ k∈Finset.range 12,v k) - _ at left
  constructor <;> linarith

theorem factored_negative_16_samples (M : ℕ) {t a : ℝ} {p : PrimalThetaParameters} (ps : p.Sound t a)
    {f : Fin 6 → FactoredFrequency} (fs : ∀ n : Fin 6, (f n).Sound t a n)
    {node : Fin 16 → Fin 6 → CGrid}
    (ns : ∀ (k : Fin 16) (n : Fin 6), (node k n).Contains (wavePhase n (-1+(k:ℝ)/16)))
    (ht : 9/10≤t) (hu : t≤7/5)
    (edge : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 →
      ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤(M:ℝ))
    (l u : ℕ → ℚ) (lo hi : ℚ)
    (good : ∀ k : Fin 16, containedInReported (sampledFactoredPrimal p f (node k)).re (l k) (u k)=true)
    (small : lo≤(∑ k∈Finset.range 16,l k)/16-(2*(M:ℚ)/(50000000-1)) ∧ (∑ k∈Finset.range 16,u k)/16+(2*(M:ℚ)/(50000000-1))≤hi) :
    (lo:ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(hi:ℝ) := by
  have hj (k : Fin 16) (j : Fin 5) := factored_sample_jets fs (ns k) (by linarith) hu j
  have bounds (k : Fin 16) := containedInReported_sound
    (primalValueOfJets_sound ps (fun j => (hj k j).1) (fun j => (hj k j).2)).1 (good k)
  let v := fun k : ℕ => (thetaA t a (((-1+(k:ℝ)/16:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re
  have low : (∑ k∈Finset.range 16,(l k:ℝ))≤∑ k∈Finset.range 16,v k :=
    Finset.sum_le_sum (fun k hk => (bounds ⟨k,Finset.mem_range.mp hk⟩).1)
  have high : (∑ k∈Finset.range 16,v k)≤∑ k∈Finset.range 16,(u k:ℝ) :=
    Finset.sum_le_sum (fun k hk => (bounds ⟨k,Finset.mem_range.mp hk⟩).2)
  have L := (Rat.cast_le (K:=ℝ)).mpr small.1
  have U := (Rat.cast_le (K:=ℝ)).mpr small.2
  push_cast at L U
  obtain ⟨left,right⟩ := abs_le.mp (negative_short_node_error (N:=16) (D:=50000000) (by decide) (by decide) negative_rate_sixteen ht edge)
  change _* (∑ k∈Finset.range 16,v k) - _≤_ at right
  change _≤_* (∑ k∈Finset.range 16,v k) - _ at left
  constructor <;> linarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_negative_12_samples
#print axioms TwoAxisHelicoid.PdfVertical.factored_negative_16_samples
