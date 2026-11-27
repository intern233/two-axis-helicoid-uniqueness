import TwoAxisHelicoid.PdfChordGroupP225L0

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def meshP225 : HorizontalRectangle :=
  ⟨(551/3200),(559/3200),(3298613772845/6597069766656),(1099542302617/2199023255552),(1066933593525215966957596005863809/5070602400912917605986812821504),(4139788200698124495204058586483829/5070602400912917605986812821504),(-3132663818358456859021807977388579/10141204801825835211973625643008),(1565585967865939474605195313861359/5070602400912917605986812821504),true,
  [((-16383/16384),2), ((-8191/8192),2), ((-16381/16384),2), ((-4095/4096),2), ((-2047/2048),2), ((-1023/1024),2), ((-511/512),2), ((-255/256),2), ((-127/128),2), ((-63/64),2), ((-31/32),2), ((-15/16),2), ((-7/8),2), ((-3/4),2), ((-1/2),2), (0,2), ((1/2),2), ((3/4),2), ((7/8),2), ((15/16),2), ((31/32),2), ((63/64),2), ((127/128),2), ((255/256),2), ((511/512),2), ((1023/1024),2), ((2047/2048),2), ((4095/4096),2), ((16381/16384),2), ((8191/8192),2), ((16383/16384),2), (1,2)]⟩

private theorem meshP225L0ok : horizontalRectanglePieces meshP225 0 0 (551/3200) (559/3200) (3298613772845/6597069766656) (1099542302617/2199023255552)=true :=
  horizontalRectangleCheck_of_output meshP225L0P_eq meshP225L0T0 (by decide +kernel)

theorem meshP225_checked : horizontalRectanglePieces meshP225 0 0 meshP225.tLo meshP225.tHi meshP225.aLo meshP225.aHi=true :=
  meshP225L0ok

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.meshP225_checked
