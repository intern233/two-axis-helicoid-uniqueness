import TwoAxisHelicoid.CentralGaussRatioTopGroup000
import TwoAxisHelicoid.CentralGaussRatioTopGroup001
import TwoAxisHelicoid.CentralGaussRatioTopGroup002
import TwoAxisHelicoid.CentralGaussRatioTopGroup003
namespace TwoAxisHelicoid
theorem centralGaussRatioTopCover : CheckedCentralRatioJets false false (7/16) (1/2) (3/5) :=
  (.join (.join checkedCentralGaussRatioTopGroup000 checkedCentralGaussRatioTopGroup001) (.join checkedCentralGaussRatioTopGroup002 checkedCentralGaussRatioTopGroup003))
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.centralGaussRatioTopCover
