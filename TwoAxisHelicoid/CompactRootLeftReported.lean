import TwoAxisHelicoid.CompactHorizontalLeftSums
import TwoAxisHelicoid.CompactRootStripAll
import TwoAxisHelicoid.PdfRootEndpointAbscissas

namespace TwoAxisHelicoid
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem original_compact_root_left_horizontal_interval : ((317389346370953943564367760022705118429661074717/50216813883093446110686315385661331328818843555712276103168):ℝ)≤thetaHorizontalPeriod ((54139230899/62500000000):ℝ) (verticalA ((54139230899/62500000000):ℝ)) ∧ thetaHorizontalPeriod ((54139230899/62500000000):ℝ) (verticalA ((54139230899/62500000000):ℝ))≤((317389359837432925716169499539170879672030303517/50216813883093446110686315385661331328818843555712276103168):ℝ) := by
  let a := verticalA ((54139230899/62500000000):ℝ)
  have ab := pdf_root_endpoint_narrow_abscissas.1
  have al : ((1469895579284285760424119244853/2475880078570760549798248448000):ℝ)≤a := by simpa only [a,Rat.cast_div,Rat.cast_ofNat] using ab.1.le
  have au : a≤((1469895579284285760424119248853/2475880078570760549798248448000):ℝ) := by simpa only [a,Rat.cast_div,Rat.cast_ofNat] using ab.2.le
  have sum := compactHorizontalLeftSum0_32 al au
  have strip := @PdfVertical.compact_original_root_strip ((54139230899/62500000000):ℝ) a (by norm_num) (by norm_num) (by linarith) (by linarith)
  have disc := PdfVertical.compact_root_theta_sampling (by norm_num) strip
  change |(1/32:ℝ)*horizontalSamplePrefix ((54139230899/62500000000):ℝ) a 32 32-thetaHorizontalPeriod ((54139230899/62500000000):ℝ) a|≤1/10^20 at disc
  have zero : horizontalSamplePrefix ((54139230899/62500000000):ℝ) a 32 0=0 := by simp [horizontalSamplePrefix]
  push_cast at sum
  rw [zero,sub_zero] at sum
  obtain ⟨l,u⟩ := abs_le.mp disc
  change _≤thetaHorizontalPeriod _ a ∧ thetaHorizontalPeriod _ a≤_
  constructor <;> linarith [sum.1,sum.2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_compact_root_left_horizontal_interval
