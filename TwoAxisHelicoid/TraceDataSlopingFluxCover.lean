import TwoAxisHelicoid.TraceDataSlopingFluxGroup00
import TwoAxisHelicoid.TraceDataSlopingFluxGroup01
import TwoAxisHelicoid.TraceDataSlopingFluxGroup02
import TwoAxisHelicoid.TraceDataSlopingFluxGroup03
import TwoAxisHelicoid.TraceDataSlopingFluxGroup04
import TwoAxisHelicoid.TraceDataSlopingFluxGroup05
import TwoAxisHelicoid.TraceDataSlopingFluxGroup06
import TwoAxisHelicoid.TraceDataSlopingFluxGroup07
import TwoAxisHelicoid.TraceDataSlopingFluxGroup08
import TwoAxisHelicoid.TraceDataSlopingFluxGroup09
import TwoAxisHelicoid.TraceDataSlopingFluxGroup10
import TwoAxisHelicoid.TraceDataSlopingFluxGroup11
import TwoAxisHelicoid.TraceDataSlopingFluxGroup12
import TwoAxisHelicoid.TraceDataSlopingFluxGroup13
import TwoAxisHelicoid.TraceDataSlopingFluxGroup14
import TwoAxisHelicoid.TraceDataSlopingFluxGroup15
import TwoAxisHelicoid.TraceDataSlopingFluxGroup16
import TwoAxisHelicoid.TraceDataSlopingFluxGroup17
import TwoAxisHelicoid.TraceDataSlopingFluxGroup18
import TwoAxisHelicoid.TraceDataSlopingFluxGroup19
import TwoAxisHelicoid.TraceDataSlopingFluxGroup20
import TwoAxisHelicoid.TraceDataSlopingFluxGroup21
import TwoAxisHelicoid.TraceDataSlopingFluxGroup22
import TwoAxisHelicoid.TraceDataSlopingFluxGroup23
namespace TwoAxisHelicoid.TraceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem original_sloping_flux_checked_cover : CheckedSlopingFluxCover slopingFluxDataSetup slopingFluxParams slopingFluxWeight.output (0/1) (1/1) := (.join (.join (.join (.join slopingFluxGroup00 (.join slopingFluxGroup01 slopingFluxGroup02)) (.join slopingFluxGroup03 (.join slopingFluxGroup04 slopingFluxGroup05))) (.join (.join slopingFluxGroup06 (.join slopingFluxGroup07 slopingFluxGroup08)) (.join slopingFluxGroup09 (.join slopingFluxGroup10 slopingFluxGroup11)))) (.join (.join (.join slopingFluxGroup12 (.join slopingFluxGroup13 slopingFluxGroup14)) (.join slopingFluxGroup15 (.join slopingFluxGroup16 slopingFluxGroup17))) (.join (.join slopingFluxGroup18 (.join slopingFluxGroup19 slopingFluxGroup20)) (.join slopingFluxGroup21 (.join slopingFluxGroup22 slopingFluxGroup23)))))
end TwoAxisHelicoid.TraceData
