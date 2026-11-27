import TwoAxisHelicoid.PdfFactoredPrimalValues
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.PdfNegativePrimalSampling

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

def sampledFactoredHeat (p : HeatGridParameters) (f : Fin 6 → FactoredFrequency) (node : Fin 6 → CGrid) : CGrid :=
  heatValueOfJets p (fun j => factoredJet f node j false) (fun j => factoredJet f node j true)

def sampledFactoredPrimal (p : PrimalThetaParameters) (f : Fin 6 → FactoredFrequency) (node : Fin 6 → CGrid) : CGrid :=
  primalValueOfJets p (fun j => factoredJet f node j false) (fun j => factoredJet f node j true)

theorem factored_heat_32_samples {t a : ℝ} {p : HeatGridParameters} (ps : p.Sound t a)
    {f : Fin 6 → FactoredFrequency} (fs : ∀ n : Fin 6, (f n).Sound t a n)
    {node : Fin 32 → Fin 6 → CGrid}
    (ns : ∀ (k : Fin 32) (n : Fin 6), (node k n).Contains (wavePhase n (2*((k:ℝ)/32)-1)))
    (ht : 17/20≤t) (hu : t≤9/10)
    (edge : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 1 → |z.im|=3/16 →
      ‖pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re) (z+I*((t/2:ℝ):ℂ))‖≤10^7)
    (u : ℕ → ℚ) (cap : ℚ)
    (good : ∀ k : Fin 32, containedInReported (sampledFactoredHeat p f (node k)).re (-10000) (u k)=true)
    (small : (∑ k∈Finset.range 32,u k)/32+1/5≤cap) : reportedHeatPeriod t a≤(cap:ℝ) := by
  have hj (k : Fin 32) (j : Fin 5) := factored_sample_jets fs (ns k) ht (hu.trans (by norm_num)) j
  have bounds (k : Fin 32) := (containedInReported_sound
    (heatValueOfJets_sound ps (fun j => (hj k j).1) (fun j => (hj k j).2)).1 (good k)).2
  have total : (∑ k∈Finset.range 32, (pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re)
    (((2*((k:ℝ)/32)-1:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)≤∑ k∈Finset.range 32,(u k:ℝ) :=
    Finset.sum_le_sum (fun k hk => bounds ⟨k,Finset.mem_range.mp hk⟩)
  have capReal := (Rat.cast_le (K:=ℝ)).mpr small
  push_cast at capReal
  have err := (abs_le.mp (pdf_heat_32_point_period_error ht edge)).1
  unfold reportedHeatPeriod
  linarith

theorem factored_negative_24_samples {t a : ℝ} {p : PrimalThetaParameters} (ps : p.Sound t a)
    {f : Fin 6 → FactoredFrequency} (fs : ∀ n : Fin 6, (f n).Sound t a n)
    {node : Fin 24 → Fin 6 → CGrid}
    (ns : ∀ (k : Fin 24) (n : Fin 6), (node k n).Contains (wavePhase n (-1+(k:ℝ)/24)))
    (ht : 9/10≤t) (hu : t≤7/5)
    (edge : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 →
      ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤10^7)
    (l u : ℕ → ℚ) (lo hi : ℚ)
    (good : ∀ k : Fin 24, containedInReported (sampledFactoredPrimal p f (node k)).re (l k) (u k)=true)
    (small : lo≤(∑ k∈Finset.range 24,l k)/24-1/1000 ∧ (∑ k∈Finset.range 24,u k)/24+1/1000≤hi) :
    (lo:ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(hi:ℝ) := by
  have hj (k : Fin 24) (j : Fin 5) := factored_sample_jets fs (ns k) (by linarith) hu j
  have bounds (k : Fin 24) := containedInReported_sound
    (primalValueOfJets_sound ps (fun j => (hj k j).1) (fun j => (hj k j).2)).1 (good k)
  let v := fun k : ℕ => (thetaA t a (((-1+(k:ℝ)/24:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re
  have low : (∑ k∈Finset.range 24,(l k:ℝ))≤∑ k∈Finset.range 24,v k :=
    Finset.sum_le_sum (fun k hk => (bounds ⟨k,Finset.mem_range.mp hk⟩).1)
  have high : (∑ k∈Finset.range 24,v k)≤∑ k∈Finset.range 24,(u k:ℝ) :=
    Finset.sum_le_sum (fun k hk => (bounds ⟨k,Finset.mem_range.mp hk⟩).2)
  have L := (Rat.cast_le (K:=ℝ)).mpr small.1
  have U := (Rat.cast_le (K:=ℝ)).mpr small.2
  push_cast at L U
  obtain ⟨left,right⟩ := abs_le.mp (negative_24_point_error ht edge)
  change _* (∑ k∈Finset.range 24,v k) - _≤_ at right
  change _≤_* (∑ k∈Finset.range 24,v k) - _ at left
  constructor <;> linarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_heat_32_samples
#print axioms TwoAxisHelicoid.PdfVertical.factored_negative_24_samples

