import TwoAxisHelicoid.MarkedTorusCircleCoordinates
import TwoAxisHelicoid.RectangleIntermediateValue
import Mathlib.Topology.TietzeExtension

namespace TwoAxisHelicoid
open Set Complex Topology
open scoped unitInterval Topology

/-- A bounded continuous perturbation of the identity of the plane
is onto. The four signs on a sufficiently large square give a
two-dimensional intermediate value proof. -/
theorem bounded_plane_displacement_surjective {v : ℂ → ℂ} (cv : Continuous v)
    (bd : ∃ B : ℝ, ∀ z, ‖v z‖≤B) : Function.Surjective (fun z : ℂ => z-v z) := by
  intro w
  obtain ⟨B,bound⟩ := bd
  let r := B+1
  let g := fun t : unitInterval × unitInterval =>
    w+(⟨r*(2*t.1.1-1),r*(2*t.2.1-1)⟩:ℂ)
  let F := fun t => g t-v (g t)-w
  have cg : Continuous g := continuous_const.add (equivRealProdCLM.symm.continuous.comp
    ((show Continuous (fun t : unitInterval × unitInterval => r*(2*t.1.1-1)) by fun_prop).prodMk
     (show Continuous (fun t : unitInterval × unitInterval => r*(2*t.2.1-1)) by fun_prop)))
  have cf : Continuous F := (cg.sub (cv.comp cg)).sub continuous_const
  have real (q) := (abs_re_le_norm (v (g q))).trans (bound _)
  have imag (q) := (abs_im_le_norm (v (g q))).trans (bound _)
  have rpart (q) : (F q).re=r*(2*q.1.1-1)-(v (g q)).re := by simp [F,g]; ring
  have ipart (q) : (F q).im=r*(2*q.2.1-1)-(v (g q)).im := by simp [F,g]; ring
  obtain ⟨t,ht⟩ := rectangle_intermediate_value_two_coordinates F cf
    (fun y => by rw [rpart]; change r*(2*0-1)-_≤0; dsimp [r]; linarith [(abs_le.mp (real (0,y))).1])
    (fun y => by rw [rpart]; change 0≤r*(2*1-1)-_; dsimp [r]; linarith [(abs_le.mp (real (1,y))).2])
    (fun x => by rw [ipart]; change r*(2*0-1)-_<0; dsimp [r]; linarith [(abs_le.mp (imag (x,0))).1])
    (fun x => by rw [ipart]; change 0<r*(2*1-1)-_; dsimp [r]; linarith [(abs_le.mp (imag (x,1))).2])
  exact ⟨g t,sub_eq_zero.mp ht⟩

/-- Two closed subsets covering the torus cannot both lift their
circle coordinates to real functions. It suffices to lift the first
coordinate on one subset and the second coordinate on the other. -/
theorem torus_closed_cover_lift_obstruction {A B : Set (Circle × Circle)} (ca : IsClosed A) (cb : IsClosed B)
    (cover : ∀ q, q∈A ∨ q∈B) (u : C(A,ℝ)) (v : C(B,ℝ))
    (first : ∀ q : A, normalizedPhase (u q)=q.1.1) (second : ∀ q : B, normalizedPhase (v q)=q.1.2) : False := by
  obtain ⟨U,hu⟩ := ContinuousMap.exists_restrict_eq ca u
  obtain ⟨V,hv⟩ := ContinuousMap.exists_restrict_eq cb v
  let π := fun z : ℂ => (normalizedPhase z.re,normalizedPhase z.im)
  let G := fun q : Circle × Circle => (⟨U q,V q⟩:ℂ)
  have phase : Continuous normalizedPhase := Circle.exp.continuous.comp (continuous_const.mul continuous_id)
  have cp : Continuous π := (phase.comp continuous_re).prodMk (phase.comp continuous_im)
  have cg : Continuous G := equivRealProdCLM.symm.continuous.comp (U.continuous.prodMk V.continuous)
  obtain ⟨b,bound⟩ := isCompact_univ.exists_bound_of_continuousOn cg.continuousOn
  obtain ⟨z,eq⟩ := bounded_plane_displacement_surjective (cg.comp cp)
    ⟨b,fun w => bound (π w) (mem_univ _)⟩ (⟨1/2,1/2⟩:ℂ)
  have no {x y : ℝ} (same : normalizedPhase x=normalizedPhase y) (diff : x-y=1/2) : False := by
    obtain ⟨k,hk⟩ := (normalizedPhase_eq_iff x y).mp same
    have pos : (0:ℤ)<k := by exact_mod_cast (show (0:ℝ)<(k:ℝ) by linarith)
    have ltone : k<(1:ℤ) := by exact_mod_cast (show (k:ℝ)<(1:ℝ) by linarith)
    omega
  rcases cover (π z) with ha|hb
  · let q : A := ⟨π z,ha⟩
    have value : U (π z)=u q := DFunLike.congr_fun hu q
    exact no ((first q).symm.trans (congrArg normalizedPhase value.symm)) (congrArg Complex.re eq)
  · let q : B := ⟨π z,hb⟩
    have value : V (π z)=v q := DFunLike.congr_fun hv q
    exact no ((second q).symm.trans (congrArg normalizedPhase value.symm)) (congrArg Complex.im eq)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_plane_displacement_surjective
#print axioms TwoAxisHelicoid.torus_closed_cover_lift_obstruction
