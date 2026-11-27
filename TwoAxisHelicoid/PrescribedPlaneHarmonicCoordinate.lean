import TwoAxisHelicoid.CompactPlaneMetricEllipticity
import TwoAxisHelicoid.FrozenHarmonicScalar
import TwoAxisHelicoid.RescaledHarmonicCoordinate

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped ContDiff

/-- Every smooth positive planar metric, Euclidean outside a compact set and
normalized to determinant one, has a local harmonic scalar with the specified
unit horizontal derivative at the prescribed point. -/
theorem compact_unit_metric_has_prescribed_harmonic_coordinate : CompactUnitMetricScalarExists := by
  intro A B C sa sb sc ha det data p
  obtain ⟨K,hK,off⟩ := data
  obtain ⟨k,k1,ell⟩ := compact_unit_plane_metric_ellipticity sa.continuous sc.continuous ha det hK off
  obtain ⟨s,v,sp,_,sv,dx,harm⟩ := exists_rescaled_harmonic_scalar sa sb sc p (show 0<k by linarith)
    (fun z x y => (ell z x y).1)
  obtain ⟨u,first,eq⟩ := rescaled_scalar_pullback sa sb sc p sp sv dx harm
  exact ⟨s,u,sp,first,eq⟩

theorem smooth_plane_metric_has_isothermal_coordinates : LocalSmoothMetricIsothermalCoordinates :=
  isothermal_coordinates_of_scalar_harmonic_existence
    (scalar_elliptic_existence_iff_compact_unit_metric.mpr compact_unit_metric_has_prescribed_harmonic_coordinate)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_unit_metric_has_prescribed_harmonic_coordinate
#print axioms TwoAxisHelicoid.smooth_plane_metric_has_isothermal_coordinates
