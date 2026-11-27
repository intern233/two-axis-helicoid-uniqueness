import TwoAxisHelicoid.PdfVerticalBoxCheck

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rightEndpointLowerCut : verticalCover false (141/100) (9/10) (63756382130020915978949311/1237940039285380274899124224) 100 (7/5) [(2241/1600),(1121/800),(561/400),(281/200),(141/100)]=true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightEndpointLowerCut
