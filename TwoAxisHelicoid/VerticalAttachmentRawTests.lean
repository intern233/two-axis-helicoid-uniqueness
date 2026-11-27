module

public import TwoAxisHelicoid.VerticalAttachmentArithmetic

@[expose] public section
namespace TwoAxisHelicoid.VerticalAttachment

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- The finer Taylor enclosure for the true nome also certifies the raw
40-term interval returned by the uploaded program at the left test point. -/
theorem left_raw_tests : VerticalRunCore.Tests left
    (10765392093268113736230733970338727/10^35) (10765392093268113736230733970338728/10^35)
    (normalizedF left).1 (normalizedF left).2 := by
  refine ⟨VerticalRunCore.left_display.1, ?_⟩
  dsimp only [normalizedF]
  rw [original_left_nome]
  unfold VerticalRunCore.seriesTest
  decide +kernel

theorem right_raw_tests : VerticalRunCore.Tests right
    (10765391416858600721767478766631171/10^35) (10765391416858600721767478766631172/10^35)
    (normalizedF right).1 (normalizedF right).2 := by
  refine ⟨VerticalRunCore.right_display.1, ?_⟩
  dsimp only [normalizedF]
  rw [original_right_nome]
  unfold VerticalRunCore.seriesTest
  decide +kernel

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.left_raw_tests
#print axioms TwoAxisHelicoid.VerticalAttachment.right_raw_tests
