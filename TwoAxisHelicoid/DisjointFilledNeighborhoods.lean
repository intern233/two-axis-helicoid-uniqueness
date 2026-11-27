module

public import TwoAxisHelicoid.MarkedExteriorComponent
import all TwoAxisHelicoid.MarkedExteriorComponent

public section
namespace TwoAxisHelicoid
open Set Topology

theorem fillAwayFrom_idempotent {X : Type*} [TopologicalSpace X] {p : X} {U : Set X}
    (outside : p∉U) : fillAwayFrom p (fillAwayFrom p U)=fillAwayFrom p U := by
  apply fillAwayFrom_eq_of_complement
  · exact fun hp => hp (mem_connectedComponentIn outside)
  · simpa only [fillAwayFrom,compl_compl] using
      (isPreconnected_connectedComponentIn : IsPreconnected (connectedComponentIn Uᶜ p))

/-- For disjoint connected sets, their fills away from the same exterior
point are disjoint whenever neither contains the other. This excludes
overlap of filled lifts that are nontrivial translates of one another. -/
theorem nonnested_filled_neighborhoods_disjoint {X : Type*} [TopologicalSpace X] {p : X} {U V : Set X}
    (uout : p∉U) (vout : p∉V) (uc : IsConnected U) (vc : IsConnected V)
    (filled : IsPreconnected (fillAwayFrom p V)) (apart : Disjoint U V)
    (uv : ¬fillAwayFrom p U⊆fillAwayFrom p V) (vu : ¬fillAwayFrom p V⊆fillAwayFrom p U) :
    Disjoint (fillAwayFrom p U) (fillAwayFrom p V) := by
  classical
  have exterior {A B : Set X} (a : p∉A) (connected : IsPreconnected B) (sep : Disjoint A B)
      (unnested : ¬fillAwayFrom p B⊆fillAwayFrom p A) : B⊆connectedComponentIn Aᶜ p := by
    have neg : ¬B⊆fillAwayFrom p A := fun sub =>
      unnested (by simpa only [fillAwayFrom_idempotent a] using fillAwayFrom_mono p sub)
    obtain ⟨y,yb,notin⟩ := not_subset.mp neg
    have ec : y∈connectedComponentIn Aᶜ p := Classical.not_not.mp notin
    have bsub : B⊆Aᶜ := fun z bz az => disjoint_left.mp sep az bz
    exact (connectedComponentIn_eq ec).symm ▸ connected.subset_connectedComponentIn yb bsub
  have vsub := exterior uout vc.isPreconnected apart vu
  have usub := exterior vout uc.isPreconnected apart.symm uv
  obtain ⟨y,yv⟩ := vc.nonempty
  have gsub : fillAwayFrom p V⊆Uᶜ := fun z gz uz => gz (usub uz)
  have out : fillAwayFrom p V⊆connectedComponentIn Uᶜ p :=
    (connectedComponentIn_eq (vsub yv)).symm ▸
      filled.subset_connectedComponentIn (subset_fillAwayFrom p V yv) gsub
  exact disjoint_left.mpr fun z uz vz => uz (out vz)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nonnested_filled_neighborhoods_disjoint
