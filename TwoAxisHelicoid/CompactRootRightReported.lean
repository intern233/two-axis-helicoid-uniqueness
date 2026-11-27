import TwoAxisHelicoid.CompactHorizontalRightSums
import TwoAxisHelicoid.CompactRootStripAll
import TwoAxisHelicoid.PdfRootEndpointAbscissas

namespace TwoAxisHelicoid
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem original_compact_root_right_horizontal_interval : ((-46097756206738198339541754847764846153863912105/12554203470773361527671578846415332832204710888928069025792):ℝ)≤thetaHorizontalPeriod ((173245538877/200000000000):ℝ) (verticalA ((173245538877/200000000000):ℝ)) ∧ thetaHorizontalPeriod ((173245538877/200000000000):ℝ) (verticalA ((173245538877/200000000000):ℝ))≤((-46097752840118437589784117229895587882833140393/12554203470773361527671578846415332832204710888928069025792):ℝ) := by
  let a := verticalA ((173245538877/200000000000):ℝ)
  have ab := pdf_root_endpoint_narrow_abscissas.2
  have al : ((4409686737855254420087965714223/7427640235712281649394745344000):ℝ)≤a := by simpa only [a,Rat.cast_div,Rat.cast_ofNat] using ab.1.le
  have au : a≤((4409686737855254420087965726223/7427640235712281649394745344000):ℝ) := by simpa only [a,Rat.cast_div,Rat.cast_ofNat] using ab.2.le
  have sum := compactHorizontalRightSum0_32 al au
  have strip := @PdfVertical.compact_original_root_strip ((173245538877/200000000000):ℝ) a (by norm_num) (by norm_num) (by linarith) (by linarith)
  have disc := PdfVertical.compact_root_theta_sampling (by norm_num) strip
  change |(1/32:ℝ)*horizontalSamplePrefix ((173245538877/200000000000):ℝ) a 32 32-thetaHorizontalPeriod ((173245538877/200000000000):ℝ) a|≤1/10^20 at disc
  have zero : horizontalSamplePrefix ((173245538877/200000000000):ℝ) a 32 0=0 := by simp [horizontalSamplePrefix]
  push_cast at sum
  rw [zero,sub_zero] at sum
  obtain ⟨l,u⟩ := abs_le.mp disc
  change _≤thetaHorizontalPeriod _ a ∧ thetaHorizontalPeriod _ a≤_
  constructor <;> linarith [sum.1,sum.2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_compact_root_right_horizontal_interval
