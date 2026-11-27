import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace TwoAxisHelicoid
open CategoryTheory

/-- Injectivity on the fundamental group is independent of basepoint in a
path-connected ambient surface. -/
theorem fundamental_map_injective_along_path {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X,Y)) {x y : X} (p : Path y x) (hi : Function.Injective (FundamentalGroup.map F x)) :
    Function.Injective (FundamentalGroup.map F y) := by
  let φ := FundamentalGroupoid.map F
  let e : FundamentalGroupoid.mk y ≅ FundamentalGroupoid.mk x := (Groupoid.isoEquivHom ..).symm (Path.Homotopic.Quotient.mk p)
  intro a b hab
  apply e.conj.injective
  apply hi
  apply CategoryTheory.End.ext
  change φ.map (e.conj a).asHom = φ.map (e.conj b).asHom
  rw [φ.map_conj,φ.map_conj]
  exact congrArg (fun g => ((φ.mapIso e).conj g).asHom) hab

theorem fundamental_mapOfEq_loop {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X,Y)) {x : X} {y : Y} (h : F x = y) (p : Path x x) :
    FundamentalGroup.mapOfEq F h (FundamentalGroup.fromPath (.mk p)) =
      FundamentalGroup.fromPath (.mk ((p.map F.continuous).cast h.symm h.symm)) := by
  rw [FundamentalGroup.mapOfEq_apply]
  rfl

theorem injective_fundamental_map_of_mapOfEq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X,Y)) {x : X} {y : Y} (h : F x = y) (hi : Function.Injective (FundamentalGroup.mapOfEq F h)) :
    Function.Injective (FundamentalGroup.map F x) := by
  intro a b hab
  apply hi
  unfold FundamentalGroup.mapOfEq
  rw [MonoidHom.comp_apply,MonoidHom.comp_apply,hab]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fundamental_map_injective_along_path
