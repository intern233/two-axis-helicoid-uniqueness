import TwoAxisHelicoid.CentralArcSpatialCriterion
import TwoAxisHelicoid.CentralSaddleSpatialSigns
import TwoAxisHelicoid.SymmetricCentralArc

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- The physical central level needs checks only between the first
saddle and the central half period. On this half-arc both signs are
proved in a one-sided neighborhood of the saddle. -/
theorem actual_central_half_slice_test {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z)
    (mark : X 1 1<X ((1+I*t)/2) 1) :
    let L := rhombicPeriodPair t ht
    let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X per q.1
    ∃ r : ℝ → ℝ, (∀ y∈Ioo 0 t, r y∈Ioo (0:ℝ) 1 ∧ X ((r y:ℂ)+I*y) 2=X 1 2) ∧
      ContinuousOn r (Ioo 0 t) ∧
      let Z := fun y : ℝ => (r y:ℂ)+I*y
      let F := fun y => (X (Z y) 0-X 1 0,X (Z y) 1-X 1 1)
      (∀ᶠ y in 𝓝[>] (0:ℝ), 0<(F y).1 ∧ 0<(F y).2) ∧
      (InjOn Y {q | Y q 2=X 1 2} ↔ InjOn F (Ioc 0 (t/2)) ∧
        (∀ y∈Ioo 0 (t/2), 0<(F y).1) ∧ ∀ y∈Ioc 0 (t/2), 0<(F y).2) := by
  intro L Y
  obtain ⟨r,inside,cont,sym,_,level,test⟩ := actual_central_spatial_embedding_test ht ha d per mark
  refine ⟨r,fun y hy => ⟨inside y hy,level y hy⟩,cont,?_⟩
  intro Z F
  obtain ⟨r₀,spec,_,lim,_⟩ := actual_central_height_arc ht ha d per
  have endpoint : Tendsto r (𝓝[>] 0) (𝓝 a) := lim.congr' (by
    filter_upwards [Ioo_mem_nhdsGT ht] with y hy using ((spec y hy).2 _ (inside y hy) |>.mp (level y hy)).symm)
  obtain ⟨ε,ep,quadrant⟩ := positive_spatial_quadrant_near_saddle ht ha d
  have near : ∀ᶠ y in 𝓝[>] (0:ℝ), 0<(F y).1 ∧ 0<(F y).2 := by
    filter_upwards [Ioo_mem_nhdsGT ep,endpoint.eventually (ball_mem_nhds a ep)] with y hy delta
    have signs := quadrant (r y) y (by simpa only [mem_ball,Real.dist_eq] using delta) hy
    exact ⟨sub_pos.mpr signs.1,sub_pos.mpr signs.2⟩
  have witness : ∃ u∈Ioo 0 (t/2), 0<(F u).1 := by
    have ev : ∀ᶠ y : ℝ in 𝓝[>] 0, y∈Ioo 0 (t/2) ∧ 0<(F y).1 := by
      filter_upwards [Ioo_mem_nhdsGT (half_pos ht),near] with y h p using ⟨h,p.1⟩
    exact ev.exists
  have reg {y : ℝ} (hy : y∈Ioo 0 t) : Z y∉L.lattice := rhombic_horizontal_strip_not_mem ht
    (by change (Z y).im∈Ioo 0 t; simpa [Z] using hy)
  have first : ContinuousOn (fun y => (F y).1) (Ioo 0 t) := by
    intro y hy
    have cz : ContinuousWithinAt Z (Ioo 0 t) y := (continuous_ofReal.continuousAt.comp_continuousWithinAt
      (cont y hy)).add (continuous_const.mul continuous_ofReal).continuousAt.continuousWithinAt
    exact ((continuous_apply 0).continuousAt.comp_continuousWithinAt
      ((d _ (reg hy)).continuousAt.comp_continuousWithinAt cz)).sub continuousWithinAt_const
  have mirrored (y : ℝ) (hy : y∈Ioo 0 t) : F (t-y)=(-(F y).1,(F y).2) := by
    have e : -Z y+(1+I*t)=Z (t-y) := by dsimp [Z]; rw [sym y hy]; push_cast; ring
    have val := per (-Z y) (1+I*t) L.ω₂_mem_lattice
    rw [e] at val
    have s := (explicit_centered_primitive_reflections ht d per (Z y) (reg hy)).1
    change X (-Z y)-X 1= ![-(X (Z y)-X 1) 0,(X (Z y)-X 1) 1,-(X (Z y)-X 1) 2] at s
    dsimp only [F]
    rw [val]
    exact Prod.ext (congrFun s 0) (congrFun s 1)
  have coord {u v : ℝ} (hu : u∈Ioo 0 t) (hv : v∈Ioo 0 t) : F u=F v ↔ X (Z u)=X (Z v) := by
    constructor
    · intro h
      have x := congrArg Prod.fst h
      have y := congrArg Prod.snd h
      funext j
      fin_cases j
      · exact sub_left_inj.mp x
      · exact sub_left_inj.mp y
      · exact (level u hu).trans (level v hv).symm
    · intro eq
      change (X (Z u) 0-X 1 0,X (Z u) 1-X 1 1)=(X (Z v) 0-X 1 0,X (Z v) 1-X 1 1)
      rw [eq]
  refine ⟨near,test.trans (Iff.trans ?_ (symmetric_central_arc_embedding_test ht F first mirrored witness))⟩
  exact and_congr
    ⟨fun hi _ hu _ hv e => hi hu hv ((coord hu hv).mp e),fun hi _ hu _ hv e => hi hu hv ((coord hu hv).mpr e)⟩
    (forall_congr' fun _ => forall_congr' fun _ => sub_pos.symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_central_half_slice_test
