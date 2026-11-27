import TwoAxisHelicoid.CentralBandLeftHeightGroup000
import TwoAxisHelicoid.CentralBandLeftHeightGroup001
import TwoAxisHelicoid.CentralBandLeftHeightGroup002
import TwoAxisHelicoid.CentralBandLeftHeightGroup003
import TwoAxisHelicoid.CentralBandLeftHeightGroup004
import TwoAxisHelicoid.CentralBandLeftHeightGroup005

namespace TwoAxisHelicoid
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem centralBandLeftHeightCover : CheckedCentralBandEdge .heightNeg true (1/2) (1/8) (3/8) :=
  (.join (.join checkedCentralBandLeftHeightGroup000 (.join checkedCentralBandLeftHeightGroup001 checkedCentralBandLeftHeightGroup002)) (.join checkedCentralBandLeftHeightGroup003 (.join checkedCentralBandLeftHeightGroup004 checkedCentralBandLeftHeightGroup005)))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centralBandLeftHeightCover
