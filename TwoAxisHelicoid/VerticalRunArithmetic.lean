import TwoAxisHelicoid.VerticalRunBounds
import TwoAxisHelicoid.VerticalRunCoreAgreement

namespace TwoAxisHelicoid.VerticalRun

theorem tests_of_core {t lo hi L U : ℚ}
    (ok : VerticalRunCore.Tests t lo hi L U) : ExpTest 44 t lo hi ∧ SeriesTest 40 lo hi L U := by
  obtain ⟨exponential, series⟩ := ok
  have expDegree : ((44 : ℕ) : ℚ) + 1 = 45 := by decide +kernel
  have seriesDegree : ((40 : ℕ) : ℚ) + 1 = 41 := by decide +kernel
  constructor
  · simpa only [VerticalRunCore.expTest, ExpTest, core_abs_eq,
      core_exp_cut_eq, core_exp_error_eq, expCut, expError,
      VerticalRunCore.piUpper, VerticalRunCore.piLower, piUpper, piLower, expDegree] using exponential
  · simpa only [VerticalRunCore.seriesTest, SeriesTest, core_series_cut_eq,
      VerticalRunCore.seriesTail, seriesCut, seriesTail, seriesDegree] using series

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem left_display_tests :
    ExpTest 44
        (70945978 / 10^8)
        (10765392093268113736230733970338727 / 10^35)
        (10765392093268113736230733970338728 / 10^35) ∧
      SeriesTest 40
        (10765392093268113736230733970338727 / 10^35)
        (10765392093268113736230733970338728 / 10^35)
        (-47221253557264140850267997705597 / 10^40)
        (-47221253557264140850240321370933 / 10^40) := by
  exact tests_of_core VerticalRunCore.left_display

theorem right_display_tests :
    ExpTest 44
        (70945980 / 10^8)
        (10765391416858600721767478766631171 / 10^35)
        (10765391416858600721767478766631172 / 10^35) ∧
      SeriesTest 40
        (10765391416858600721767478766631171 / 10^35)
        (10765391416858600721767478766631172 / 10^35)
        (13998405173549555596490797567326 / 10^39)
        (13998405173549555596493565200718 / 10^39) := by
  exact tests_of_core VerticalRunCore.right_display

theorem left_inner_tests :
    ExpTest 44
        (709459781 / 10^9)
        (10765392059447637076131062167372461 / 10^35)
        (10765392059447637076131062167372462 / 10^35) ∧
      SeriesTest 40
        (10765392059447637076131062167372461 / 10^35)
        (10765392059447637076131062167372462 / 10^35)
        (-1 / 10^7)
        0 := by
  exact tests_of_core VerticalRunCore.left_inner

theorem right_inner_tests :
    ExpTest 44
        (709459799 / 10^9)
        (10765391450679075363114151510334436 / 10^35)
        (10765391450679075363114151510334437 / 10^35) ∧
      SeriesTest 40
        (10765391450679075363114151510334436 / 10^35)
        (10765391450679075363114151510334437 / 10^35)
        0
        (1 / 10^7) := by
  exact tests_of_core VerticalRunCore.right_inner

end TwoAxisHelicoid.VerticalRun

#print axioms TwoAxisHelicoid.VerticalRun.left_display_tests
#print axioms TwoAxisHelicoid.VerticalRun.right_display_tests
#print axioms TwoAxisHelicoid.VerticalRun.left_inner_tests
#print axioms TwoAxisHelicoid.VerticalRun.right_inner_tests
#print axioms TwoAxisHelicoid.VerticalRun.tests_of_core
