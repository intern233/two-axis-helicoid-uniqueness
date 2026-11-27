import TwoAxisHelicoid.PhysicalSheetGerms
import TwoAxisHelicoid.GraphContactGermEquation
import TwoAxisHelicoid.ContactArcsPolar
import TwoAxisHelicoid.ConformalContactDirections

namespace TwoAxisHelicoid
open Complex Real Set Filter Topology Metric Function InnerProductSpace InnerProductGeometry
open scoped Topology ContDiff

private def EqualAngleContactArcs.shrink {f : ℂ → ℝ} {a : ℂ} (K : EqualAngleContactArcs f a)
    (r : ℝ) (positive : 0<r) (sub : r≤K.radius) : EqualAngleContactArcs f a :=
  { K with
    radius := r
    radius_pos := positive
    regular := fun i => (K.regular i).mono (fun _ h => ⟨h.1,h.2.trans_le sub⟩)
    vanishes := fun i s h => K.vanishes i s ⟨h.1,h.2.trans_le sub⟩
    separated := fun i j s t hs ht => K.separated i j s t ⟨hs.1,hs.2.trans_le sub⟩ ⟨ht.1,ht.2.trans_le sub⟩
    covers := fun z pos small => K.covers z pos (small.trans_le sub) }

/-- Two tangent regular minimal sheets either coincide as local graph
sheets or meet along exactly 2n distinct half-arcs for n ≥ 2. The
parametrization uses the first sheet's own conformal coordinate. The
tangent vectors and their consecutive angles are measured in the
original Euclidean space. -/
theorem equal_angle_intersection_of_minimal_sheets {X Y : ℂ → Fin 3 → ℝ} {a b : ℂ}
    (hx : ∀ᶠ z in 𝓝 a, (∀ j, HarmonicAt (fun u => X u j) z) ∧ ConformalCoordinateDerivatives X z)
    (hy : ∀ᶠ z in 𝓝 b, (∀ j, HarmonicAt (fun u => Y u j) z) ∧ ConformalCoordinateDerivatives Y z)
    (ix : Injective (fderiv ℝ X a)) (iy : Injective (fderiv ℝ Y b)) (meet : X a=Y b)
    (same : (fderiv ℝ X a).range=(fderiv ℝ Y b).range) {V₀ : Set ℂ} (nbd : V₀∈𝓝 b) :
    ∃ V∈𝓝 b, V⊆V₀ ∧ InjOn Y V ∧
      ((∀ U₀∈𝓝 a, ∃ U W : Set ℂ, IsOpen U ∧ IsOpen W ∧ a∈U ∧ b∈W ∧ U⊆U₀ ∧ W⊆V ∧
        InjOn X U ∧ InjOn Y W ∧ X '' U=Y '' W) ∨
      ∃ (f : ℂ → ℝ) (K : EqualAngleContactArcs f a),
        InjOn X (Metric.ball a K.radius) ∧
        (∀ z, 0<dist z a → dist z a<K.radius →
          (X z∈Y '' V ↔ ∃ i, z=K.arm i (dist z a))) ∧
        (∀ i, HasDerivAt (coordinateToEuclidean ∘ X ∘ K.arm i)
          (fderiv ℝ (coordinateToEuclidean ∘ X) a (circleMap 0 1 (contactArmAngle K.order K.coefficient i.1))) 0) ∧
        ∀ k : ℤ, let D := fderiv ℝ (coordinateToEuclidean ∘ X) a
          angle (D (circleMap 0 1 (contactArmAngle K.order K.coefficient k)))
            (D (circleMap 0 1 (contactArmAngle K.order K.coefficient (k+1))))=Real.pi/K.order) := by
  have ax : AnalyticAt ℝ X a := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hx.self_of_nhds.1 j))
  have ay : AnalyticAt ℝ Y b := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hy.self_of_nhds.1 j))
  obtain ⟨P,e,d,ea,db,ex,dy⟩ := tangent_sheet_projection_charts ax.contDiffAt ay.contDiffAt ix iy same
  obtain ⟨V,f,A,B,vn,sub,an,touch,flat,ca,cb,pde,exactSet⟩ := tangent_minimal_sheet_germ_equation hx hy ix iy meet same
    (inter_mem nbd (d.open_source.mem_nhds db))
  have vd : V⊆d.source := sub.trans inter_subset_right
  refine ⟨V,vn,sub.trans inter_subset_left,?_,?_⟩
  · intro z hz w hw eq
    exact d.injOn (vd hz) (vd hw) ((dy z).trans ((congrArg P eq).trans (dy w).symm))
  by_cases zeros : f =ᶠ[𝓝 a] 0
  · left
    intro U₀ un
    apply equal_open_sheet_patches ea db ex dy meet un vd
    filter_upwards [zeros,exactSet] with z hz eq
    exact eq.mp hz
  · obtain ⟨K⟩ := analytic_drift_equal_angle_contact an touch flat zeros ca cb pde
    obtain ⟨r,rp,localEq⟩ := Metric.mem_nhds_iff.mp (inter_mem (e.open_source.mem_nhds ea) exactSet)
    let S := K.shrink (min K.radius r) (lt_min K.radius_pos rp) (min_le_left _ _)
    have dx := ax.differentiableAt
    refine Or.inr ⟨f,S,?_,?_,?_,equal_angle_in_physical_tangent_plane dx hx.self_of_nhds.2 ix S.at_least_two S.coefficient⟩
    · intro z hz w hw eq
      have lift {q : ℂ} (hq : q∈Metric.ball a S.radius) : q∈e.source :=
        (localEq (show q∈Metric.ball a r from (show dist q a<S.radius from hq).trans_le (min_le_right _ _))).1
      exact e.injOn (lift hz) (lift hw) ((ex z).trans ((congrArg P eq).trans (ex w).symm))
    · intro z pos small
      have loc := (localEq (show z∈Metric.ball a r from small.trans_le (min_le_right _ _))).2
      change f z=0 ↔ X z∈Y '' V at loc
      rw [← loc]
      refine ⟨S.covers z pos small,?_⟩
      rintro ⟨i,h⟩
      exact (congrArg f h).trans (S.vanishes i _ ⟨pos,small⟩)
    · intro i
      let D := fderiv ℝ (coordinateToEuclidean ∘ X) a
      have der : HasFDerivAt (coordinateToEuclidean ∘ X) D (S.arm i 0) := by
        rw [S.center]
        exact (coordinateToEuclidean.differentiableAt.comp a dx).hasFDerivAt
      exact der.comp_hasDerivAt 0 (S.tangent i)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.equal_angle_intersection_of_minimal_sheets
