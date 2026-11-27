import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The margins printed in the two original interval-cover summaries. -/
def originalPositiveMargin : ℚ := 4048815533235523741519408834611 / 10384593717069655257060992658440192
def originalNegativeMargin : ℚ := 238070159187588210339310175778799 / 5192296858534827628530496329220096

theorem original_sign_summary_extrema :
    (∀ r∈positiveData, originalPositiveMargin≤r.hReal.lower) ∧
    (positiveData.map (fun r => r.hReal.lower))[557]?=some originalPositiveMargin ∧
    (∀ r∈negativeData, r.hReal.upper≤ -originalNegativeMargin) ∧
    (negativeData.map (fun r => r.hReal.upper))[6]?=some (-originalNegativeMargin) := by
  have p : positiveData.all (fun r => decide (originalPositiveMargin≤r.hReal.lower))=true := by decide +kernel
  have n : negativeData.all (fun r => decide (r.hReal.upper≤ -originalNegativeMargin))=true := by decide +kernel
  exact ⟨fun r hr => of_decide_eq_true (List.all_eq_true.mp p r hr),by decide +kernel,
    fun r hr => of_decide_eq_true (List.all_eq_true.mp n r hr),by decide +kernel⟩

/-- Extend the row enclosures to the exact global margin for every real
height in the closed positive or negative interval. -/
theorem original_summary_margins_of_enclosures (H : ℝ → ℝ)
    (hp : ∀ r∈positiveData, ∀ t : ℝ, RealMem r.t t → RealMem r.hReal (H t))
    (hn : ∀ r∈negativeData, ∀ t : ℝ, RealMem r.t t → RealMem r.hReal (H t)) :
    (∀ t∈Set.Icc (1/8:ℝ) (17/20), (originalPositiveMargin:ℝ)≤H t) ∧
    ∀ t∈Set.Icc (9/10:ℝ) (7/5), H t≤ -(originalNegativeMargin:ℝ) := by
  obtain ⟨pe,_,ne,_⟩ := original_sign_summary_extrema
  constructor
  · intro t ht
    obtain ⟨r,hr,h⟩ := checked_sign_row_covers positive_partition (by norm_num) (x:=t)
      (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Set.mem_Icc] using ht)
    exact ((Rat.cast_le (K:=ℝ)).mpr (pe r hr)).trans (hp r hr t h).1
  · intro t ht
    obtain ⟨r,hr,h⟩ := checked_sign_row_covers negative_partition (by norm_num) (x:=t)
      (by simpa only [Rat.cast_div,Rat.cast_ofNat,Set.mem_Icc] using ht)
    exact (hn r hr t h).2.trans (by exact_mod_cast ne r hr)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_sign_summary_extrema
#print axioms TwoAxisHelicoid.PdfVertical.original_summary_margins_of_enclosures

