import TwoAxisHelicoid.DifferentiableSaddleChart
import TwoAxisHelicoid.TorusMorseLevelGerms
import TwoAxisHelicoid.TiltedHeightRegularCoordinates
import TwoAxisHelicoid.TiltedComponentSpinParity
import TwoAxisHelicoid.EssentialTorusHeightComponent

namespace TwoAxisHelicoid
open Complex Set Filter Topology MeasureTheory
open scoped Topology ContDiff Manifold

/-- A nonlifting component of a physical plane section contains the
unique saddle at its height. The marking, the full height on the
torus, and the local crossed-axes model refer to the same point. -/
def HasNonliftingSingleSaddle (L : PeriodPair) (H : PeriodTorus L ≃ₜ Circle×Circle)
    (h : PeriodTorus L → ℝ) : Prop :=
  ∃ (v : ℝ) (x p : h ⁻¹' {v}) (e : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ)),
    v≠h 0 ∧ p∈connectedComponent x ∧ p.1∈e.source ∧ e p.1=0 ∧
    (∀ᶠ q in 𝓝 p.1, h q=h p.1+(e q).1*(e q).2) ∧
    (∃ z, periodTorusProjection L z=p.1 ∧ ContDiffAt ℝ 1 (e ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (e ∘ periodTorusProjection L) z)) ∧
    (∀ z, h (periodTorusProjection L z)=v →
      (fderiv ℝ (h ∘ periodTorusProjection L) z=0 ↔ periodTorusProjection L z=p.1)) ∧
    ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2

/-- Given regularity in its genuine chart at the filled point,
an odd spatial torus would have a nonlifting component containing a
single Morse saddle for almost every tilt. Regular components and both
types of extrema are excluded using the actual height function. -/
theorem odd_embedded_torus_has_single_saddle_section (L : PeriodPair)
    (F : PeriodTorus L → Fin 3 → ℝ) (cont : Continuous F) (emb : Function.Injective F)
    (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (d : OpenPartialHomeomorph (PeriodTorus L) ℂ) (src : (0:PeriodTorus L)∈d.source)
    (dsm : ContDiffAt ℝ ∞ (F ∘ d.symm) (d 0)) (dim : Function.Injective (fderiv ℝ (F ∘ d.symm) (d 0)))
    (H : PeriodTorus L ≃ₜ Circle×Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    (odd : capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)≠0) :
    ∀ᵐ s : ℂ, HasNonliftingSingleSaddle L H (tiltedSpatialHeight s ∘ F) ∧
      (let f := (tiltedSpatialHeight s ∘ F) ∘ periodTorusProjection L
       (f '' {z | z∉L.lattice ∧ fderiv ℝ f z=0}).Countable) := by
  classical
  let π := periodTorusProjection L
  let Y := F ∘ π
  let D := (L.lattice : Set ℂ)ᶜ
  have reg (z : ℂ) (hz : z∈D) := spatial_torus_lift_regular_at L F hz sm imm
  have sc (z : ℂ) (hz : z∈D) : ContDiffAt ℝ 3 Y z := (reg z hz).1.of_le (by simp)
  have inj (z : ℂ) (hz : z∈D) : Function.Injective (fderiv ℝ Y z) := (reg z hz).2
  filter_upwards [ae_tilted_height_differentiable_morse_charts sc inj (F 0),ae_countable_tilted_critical_values sc inj,
    ae_tilted_surface_height_chart_at_mark F 0 d src dsm dim] with s morse count atMark
  let h := tiltedSpatialHeight s ∘ F
  let f := h ∘ π
  refine ⟨?_,count⟩
  obtain ⟨v,x,obstruct⟩ := marked_height_has_essential_component H ((tiltedSpatialHeight s).continuous.comp cont)
  have criticalIn : ∃ (z : ℂ) (level : f z=v), z∈D ∧ fderiv ℝ f z=0 ∧
      (⟨π z,level⟩ : h ⁻¹' {v})∈connectedComponent x := by
    by_contra fail
    apply odd
    apply cap_even_of_regular_component_and_countable_critical_values L F cont emb sm imm H marked s v x _ obstruct count
    intro q inC
    by_cases atZero : q.1=0
    · rw [atZero]
      exact atMark
    obtain ⟨z,eq⟩ := (Quotient.mk_surjective : Function.Surjective π) q.1
    have off : z∈D := fun hz => atZero (eq.symm.trans ((periodTorusProjection_eq_zero L z).mpr hz))
    have level : f z=v := (congrArg h eq).trans q.2
    have nz : fderiv ℝ f z≠0 := fun zero => fail ⟨z,level,off,zero,
      (show (⟨π z,level⟩ : h ⁻¹' {v})=q from Subtype.ext eq).symm ▸ inC⟩
    rw [← eq]
    exact torus_height_chart_of_regular_lift L z
      ((tiltedSpatialHeight s).contDiff.contDiffAt.comp z (reg z off).1) nz
  obtain ⟨z,level,away,critical,inC⟩ := criticalIn
  let p : h ⁻¹' {v} := ⟨π z,level⟩
  obtain ⟨⟨a,b,E,aa,bb,inside,center,dE,dinv,formula⟩,separate,avoid⟩ := morse z away critical
  have distinct : v≠h 0 := by
    intro eq
    exact away ((periodTorusProjection_eq_zero L z).mp (emb (avoid (level.trans eq))))
  have uniq (w : ℂ) (hw : f w=v) : fderiv ℝ f w=0 ↔ π w=p.1 := by
    constructor
    · intro zero
      have off : w∈D := fun member => distinct (hw.symm.trans (congrArg h ((periodTorusProjection_eq_zero L w).mpr member)))
      exact emb (separate w off zero (hw.trans level.symm))
    · intro eq
      exact (torus_height_derivative_eq_of_same_projection L h (z:=w) (w:=z) eq).trans critical
  obtain ⟨e,es,ez,realizes,model⟩ := torus_morse_height_chart_of_lift_with_germ L h z E inside center formula
  have sides : b=a ∨ b= -a := by
    have prod : (b-a)*(b+a)=0 := by nlinarith [aa,bb]
    rcases mul_eq_zero.mp prod with h1|h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (by linarith)
  rcases sides with same|opposite
  · subst b
    have an : a≠0 := by intro eq; simp [eq] at aa
    have isolated := definite_morse_height_point_isolated e es ez an model
    exact False.elim (obstruct (marked_level_component_lifts_at_isolated_point H x p inC (by
      filter_upwards [isolated] with w iso
      intro hw
      exact iso (hw.trans level.symm))))
  · subst b
    obtain ⟨k,ks,kz,coord,saddle⟩ := saddle_morse_height_product_chart_with_coordinates e es ez aa model
    have neq : a≠0 := fun eq => by simp [eq] at aa
    have back : DifferentiableAt ℝ E.symm (E z) := center.symm ▸ dinv.differentiableAt one_ne_zero
    have di := saddle_chart_injective_differential E inside (dE.differentiableAt one_ne_zero) back
    have root := regular_saddle_difference_to_product neq dE di
    have physical : (k ∘ π) =ᶠ[𝓝 z] (fun w => ((E w).1-(E w).2,a*((E w).1+(E w).2))) := by
      filter_upwards [realizes] with w eq
      change e (π w)=E w at eq
      change k (π w)=_
      rw [coord,eq]
    have differentiable : ContDiffAt ℝ 1 (k ∘ π) z := root.1.congr_of_eventuallyEq physical
    have nonsingular : Function.Injective (fderiv ℝ (k ∘ π) z) := by rw [physical.fderiv_eq]; exact root.2
    exact ⟨v,x,p,k,distinct,inC,ks,kz,saddle,⟨z,rfl,differentiable,nonsingular⟩,uniq,obstruct⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.odd_embedded_torus_has_single_saddle_section
