import TwoAxisHelicoid.CentralBandRightHeightGroup000
import TwoAxisHelicoid.CentralBandRightHeightGroup001
import TwoAxisHelicoid.CentralBandRightHeightGroup002
import TwoAxisHelicoid.CentralBandRightHeightGroup003
import TwoAxisHelicoid.CentralBandRightHeightGroup004

namespace TwoAxisHelicoid
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem centralBandRightHeightCover : CheckedCentralBandEdge .heightPos true (5/8) (1/8) (3/8) :=
  (.join (.join checkedCentralBandRightHeightGroup000 checkedCentralBandRightHeightGroup001) (.join checkedCentralBandRightHeightGroup002 (.join checkedCentralBandRightHeightGroup003 checkedCentralBandRightHeightGroup004)))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centralBandRightHeightCover
