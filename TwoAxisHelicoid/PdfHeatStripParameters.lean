import TwoAxisHelicoid.PdfHeatGridKernel
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def heatStripT := Grid.ofRats (17/20) (9/10)
def heatStripP : HeatGridParameters := ⟨⟨⟨⟨71525505308257361912944,83691191781282312217787,true⟩,⟨0,0,true⟩⟩, ⟨⟨1116598027249049183012361,1150779599511844949719826,true⟩,⟨0,0,true⟩⟩, ⟨(-1564756419138205855026688),(-1496393274612683041090840),true⟩, ⟨5733103845691675726761791,6668010046172985105780570,true⟩⟩, ⟨167373693859487446585344,781819105126068979618764,true⟩, ⟨520560573232713201591292,675105446534852827169727,true⟩, ⟨(-1612414885699856254393703),(-1324933440256568732822363),true⟩, ⟨(-2923264924708573091440419),(-2560758606565265296028141),true⟩, ⟨(-614478408877778224402373),(-587632264800526520543368),true⟩⟩
theorem heatStripP_ok : heatStripP.encloses (heatGridParameters heatStripT (Grid.ofRats (147/250) (303/500))) := by decide +kernel


end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripP_ok
