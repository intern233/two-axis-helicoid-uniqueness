import TwoAxisHelicoid.CompactHorizontalLeftG0
import TwoAxisHelicoid.CompactHorizontalLeftG1
import TwoAxisHelicoid.CompactHorizontalLeftG2
import TwoAxisHelicoid.CompactHorizontalLeftG3
import TwoAxisHelicoid.CompactHorizontalLeftG4
import TwoAxisHelicoid.CompactHorizontalLeftG5
import TwoAxisHelicoid.CompactHorizontalLeftG6
import TwoAxisHelicoid.CompactHorizontalLeftG7

namespace TwoAxisHelicoid
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem compactHorizontalLeftSum0_8 {a : ℝ} (al : ((1469895579284285760424119244853/2475880078570760549798248448000):ℝ)≤a) (au : a≤((1469895579284285760424119248853/2475880078570760549798248448000):ℝ)) : (((5265636200446096739738876103290192478403/170141183460469231731687303715884105728):ℚ):ℝ)≤horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 8-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 0 ∧ horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 8-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 0≤(((5265636200446096739739049774238584884003/170141183460469231731687303715884105728):ℚ):ℝ) :=
  horizontalSamplePrefix_add_bounds (compactHorizontalLeftG0_bounds al au) (compactHorizontalLeftG1_bounds al au) (by decide +kernel) (by decide +kernel)
theorem compactHorizontalLeftSum8_16 {a : ℝ} (al : ((1469895579284285760424119244853/2475880078570760549798248448000):ℝ)≤a) (au : a≤((1469895579284285760424119248853/2475880078570760549798248448000):ℝ)) : (((3554144227328636814393353327772533085083/340282366920938463463374607431768211456):ℚ):ℝ)≤horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 16-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 8 ∧ horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 16-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 8≤(((3554144227328636814393703099520119434165/340282366920938463463374607431768211456):ℚ):ℝ) :=
  horizontalSamplePrefix_add_bounds (compactHorizontalLeftG2_bounds al au) (compactHorizontalLeftG3_bounds al au) (by decide +kernel) (by decide +kernel)
theorem compactHorizontalLeftSum16_24 {a : ℝ} (al : ((1469895579284285760424119244853/2475880078570760549798248448000):ℝ)≤a) (au : a≤((1469895579284285760424119248853/2475880078570760549798248448000):ℝ)) : (((-2763232212112332462206440428278273980323/85070591730234615865843651857942052864):ℚ):ℝ)≤horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 24-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 16 ∧ horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 24-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 16≤(((-1381616106056166231103126713531162668985/42535295865117307932921825928971026432):ℚ):ℝ) :=
  horizontalSamplePrefix_add_bounds (compactHorizontalLeftG4_bounds al au) (compactHorizontalLeftG5_bounds al au) (by decide +kernel) (by decide +kernel)
theorem compactHorizontalLeftSum24_32 {a : ℝ} (al : ((1469895579284285760424119244853/2475880078570760549798248448000):ℝ)≤a) (au : a≤((1469895579284285760424119248853/2475880078570760549798248448000):ℝ)) : (((-3032487779702677599814869656155788260733/340282366920938463463374607431768211456):ℚ):ℝ)≤horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 32-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 24 ∧ horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 32-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 24≤(((-3032487779702677599813528943813932885803/340282366920938463463374607431768211456):ℚ):ℝ) :=
  horizontalSamplePrefix_add_bounds (compactHorizontalLeftG6_bounds al au) (compactHorizontalLeftG7_bounds al au) (by decide +kernel) (by decide +kernel)
theorem compactHorizontalLeftSum0_16 {a : ℝ} (al : ((1469895579284285760424119244853/2475880078570760549798248448000):ℝ)≤a) (au : a≤((1469895579284285760424119248853/2475880078570760549798248448000):ℝ)) : (((14085416628220830293871105534352918041889/340282366920938463463374607431768211456):ℚ):ℝ)≤horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 16-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 0 ∧ horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 16-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 0≤(((14085416628220830293871802647997289202171/340282366920938463463374607431768211456):ℚ):ℝ) :=
  horizontalSamplePrefix_add_bounds (compactHorizontalLeftSum0_8 al au) (compactHorizontalLeftSum8_16 al au) (by decide +kernel) (by decide +kernel)
theorem compactHorizontalLeftSum16_32 {a : ℝ} (al : ((1469895579284285760424119244853/2475880078570760549798248448000):ℝ)≤a) (au : a≤((1469895579284285760424119248853/2475880078570760549798248448000):ℝ)) : (((-14085416628152007448640631369268884182025/340282366920938463463374607431768211456):ℚ):ℝ)≤horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 32-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 16 ∧ horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 32-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 16≤(((-14085416628152007448638542652063234237683/340282366920938463463374607431768211456):ℚ):ℝ) :=
  horizontalSamplePrefix_add_bounds (compactHorizontalLeftSum16_24 al au) (compactHorizontalLeftSum24_32 al au) (by decide +kernel) (by decide +kernel)
theorem compactHorizontalLeftSum0_32 {a : ℝ} (al : ((1469895579284285760424119244853/2475880078570760549798248448000):ℝ)≤a) (au : a≤((1469895579284285760424119248853/2475880078570760549798248448000):ℝ)) : (((8602855653809270635504232483/42535295865117307932921825928971026432):ℚ):ℝ)≤horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 32-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 0 ∧ horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 32-horizontalSamplePrefix (((54139230899/62500000000):ℚ):ℝ) a 32 0≤(((8602855654157499491756870561/42535295865117307932921825928971026432):ℚ):ℝ) :=
  horizontalSamplePrefix_add_bounds (compactHorizontalLeftSum0_16 al au) (compactHorizontalLeftSum16_32 al au) (by decide +kernel) (by decide +kernel)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactHorizontalLeftSum0_32
