import TwoAxisHelicoid.GeometricHelicoidHypotheses
import TwoAxisHelicoid.TorusPunctureFundamental
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace TwoAxisHelicoid
open Complex

/-- A handle loop in the punctured surface is detected by its displacement
in the compact torus. This uses the original topological type only. -/
theorem punctured_period_torus_not_simply_connected (L : PeriodPair) :
    ¬ SimplyConnectedSpace (PuncturedPeriodTorus L) := by
  intro h
  let := h
  have he := congrArg (puncturedTorusFundamentalInclusion L)
    (Subsingleton.elim (puncturedTorusGeneratorClass L 0) 1)
  rw [puncturedTorusFundamentalInclusion_generator,map_one] at he
  have hx := congrArg (periodTorusBasedFundamentalGroupEquiv L) he
  rw [periodTorusGeneratorClass_coordinates,map_one] at hx
  have hfirst := congrArg (fun p : Multiplicative (ℤ × ℤ) => p.toAdd.1) hx
  norm_num at hfirst

theorem OriginalSmoothHelicoid.not_simply_connected (surface : OriginalSmoothHelicoid) :
    ¬ SimplyConnectedSpace surface.carrier := fun h =>
  punctured_period_torus_not_simply_connected _ (surface.topologicalType.toHomotopyEquiv.simplyConnectedSpace_iff.mp h)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.not_simply_connected
