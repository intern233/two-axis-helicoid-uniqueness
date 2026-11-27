import TwoAxisHelicoid.MiddleVerticalAll
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The native vertical certificates enclose the actual branch in
the exact rational abscissa column of each original heat-table row. -/
theorem original_derivative_abscissa_rows :
    ∀ r∈derivativeData, ∀ t : ℝ, RealMem r.t t → verticalA t∈Ioo (r.a.lower:ℝ) (r.a.upper:ℝ) := by
  intro r member t tb
  simp only [derivativeData,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [RealMem,derivative_000,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox000_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_001,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox001_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_002,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox002_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_003,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox003_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_004,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox004_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_005,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox005_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_006,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox006_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_007,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox007_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_008,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox008_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_009,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox009_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_010,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox010_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_011,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox011_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_012,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox012_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_013,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox013_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_014,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox014_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_015,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox015_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_016,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox016_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_017,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox017_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_018,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox018_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_019,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox019_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_020,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox020_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_021,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox021_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_022,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox022_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_023,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox023_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_024,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox024_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_025,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox025_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_026,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox026_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_027,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox027_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_028,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox028_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_029,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox029_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_030,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox030_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_031,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox031_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_032,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox032_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_033,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox033_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_034,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox034_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_035,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox035_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_036,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox036_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_037,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox037_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_038,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox038_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_039,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox039_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_040,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox040_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_041,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox041_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_042,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox042_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_043,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox043_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_044,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox044_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_045,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox045_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_046,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox046_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_047,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox047_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_048,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox048_enclosure tb.1 tb.2
  · simp only [RealMem,derivative_049,Rat.cast_div,Rat.cast_ofNat] at tb ⊢
    exact middleVerticalBox049_enclosure tb.1 tb.2

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_derivative_abscissa_rows

