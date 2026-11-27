import TwoAxisHelicoid.RegularHorizontalFiberTangent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Topology
open scoped Interval Topology

/-- The positive Weierstrass speed times the Gauss map on a horizontal
level. Multiplication by −i gives the actual complex horizontal tangent. -/
noncomputable def horizontalWeightedGauss (t a : ℝ) (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  let G := thetaGauss t a 1 (g y)
  ((((normSq G)⁻¹+1)/2:ℝ):ℂ)*G

/-- A spatial chord of a regular horizontal fiber vanishes exactly when
the integral of its weighted Gauss map vanishes, with the actual
imaginary height as parameter and no arbitrary reparametrization. -/
theorem actual_horizontal_chord_integral {t a c s h : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z)
    {g : ℝ → ℂ} (cg : Continuous g) (off : ∀ y, g y∉(rhombicPeriodPair t ht).lattice)
    (co : ∀ y, actualComplexHeight t a c ht (g y)=⟨s,y⟩)
    (lev : ∀ y, X (g y) 2=h) (hn : h≠X 1 2) (u v : ℝ) :
    let f := fun y => ((X (g y) 0:ℝ):ℂ)+I*(X (g y) 1:ℂ)
    f v-f u= -I*(∫ y in u..v,horizontalWeightedGauss t a g y) ∧
      (X (g u)=X (g v) ↔ (∫ y in u..v,horizontalWeightedGauss t a g y)=0) := by
  intro f
  let G := fun y => thetaGauss t a 1 (g y)
  let k := fun y => ((normSq (G y))⁻¹+1)/2
  have non (y : ℝ) : X (g y) 2≠X 1 2 := (lev y).symm ▸ hn
  have regular (y : ℝ) := actual_noncentral_height_regular ht ha hc d per (off y) (non y)
  have gn (y : ℝ) : G y≠0 := thetaGauss_ne_zero ht a 1 (regular y).2.1 (regular y).2.2
  have cG : Continuous G := continuous_iff_continuousAt.mpr fun y =>
    (thetaGauss_hasDerivAt ht a 1 (off y) (regular y).2.1 (regular y).2.2).continuousAt.comp cg.continuousAt
  have ck : Continuous k := (((continuous_normSq.comp cG).inv₀ (fun y => (normSq_pos.mpr (gn y)).ne')).add continuous_const).div_const 2
  have cw : Continuous (horizontalWeightedGauss t a g) := (continuous_ofReal.comp ck).mul cG
  have der (y : ℝ) : HasDerivAt f (-I*horizontalWeightedGauss t a g y) y := by
    have vel := (actual_regular_horizontal_fiber_tangent ht ha hc d per cg co (off y) (non y)).2
    have dx := (hasDerivAt_pi.mp vel 0).ofReal_comp
    have dy := (hasDerivAt_pi.mp vel 1).ofReal_comp
    have combined := dx.add (dy.const_mul I)
    change HasDerivAt f (((k y*(G y).im:ℝ):ℂ)+I*((-(k y)*(G y).re:ℝ):ℂ)) y at combined
    convert combined using 1
    apply Complex.ext <;> simp [horizontalWeightedGauss,G,k,Complex.mul_re,Complex.mul_im]
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => der y)
    ((continuous_const.mul cw).intervalIntegrable u v (μ:=volume))
  rw [intervalIntegral.integral_const_mul] at eq
  refine ⟨eq.symm,?_⟩
  have horiz : X (g u)=X (g v) ↔ f v-f u=0 := by
    rw [sub_eq_zero]
    constructor
    · intro e
      simp only [f,e]
    · intro e
      have real := congrArg re e
      have imag := congrArg im e
      simp [f] at real imag
      funext j
      fin_cases j
      · exact real.symm
      · exact imag.symm
      · exact (lev u).trans (lev v).symm
  rw [horiz,← eq]
  simp

/-- On each noncentral physical plane, injectivity of the full spatial
level is equivalent to nonvanishing of every nontrivial chord integral
on one continuous lift of that entire level. -/
theorem actual_noncentral_level_embedding_test {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) {h : ℝ} (hn : h≠0) :
    let L := rhombicPeriodPair t ht
    let Y := fun p : PuncturedPeriodTorus L => periodTorusLift L X per p.1
    ∃ (g : ℝ → ℂ) (q : ℝ → PuncturedPeriodTorus L), Continuous g ∧ IsClosedEmbedding q ∧
      range q={p | Y p 2=X 1 2+h} ∧ (∀ y, (q y).1=periodTorusProjection L (g y)) ∧
      (InjOn Y (range q) ↔ ∀ u v, u<v → (∫ y in u..v,horizontalWeightedGauss t a g y)≠0) := by
  intro L Y
  obtain ⟨g,s,q,cg,prop,emb,rng⟩ := actual_regular_horizontal_fibers ht ha hc d per hn
  have agree (y : ℝ) : Y (q y)=X (g y) := congrArg (periodTorusLift L X per) (prop y).2.2
  have level (y : ℝ) : X (g y) 2=X 1 2+h := by
    have mem : q y∈range q := mem_range_self y
    rw [rng] at mem
    exact (congrFun (agree y) 2).symm.trans mem
  have ne : X 1 2+h≠X 1 2 := fun e => hn (by linarith)
  have iff (u v : ℝ) := (actual_horizontal_chord_integral ht ha hc d per cg (fun y => (prop y).1)
    (fun y => (prop y).2.1) level ne u v).2
  refine ⟨g,q,cg,emb,rng,fun y => (prop y).2.2,?_,?_⟩
  · intro inj u v uv zero
    have same := (agree u).trans (((iff u v).mpr zero).trans (agree v).symm)
    exact uv.ne (emb.injective (inj (mem_range_self _) (mem_range_self _) same))
  · rintro tests _ ⟨u,rfl⟩ _ ⟨v,rfl⟩ same
    have eq := (agree u).symm.trans (same.trans (agree v))
    rcases lt_trichotomy u v with uv|uv|vu
    · exact (tests u v uv ((iff u v).mp eq)).elim
    · exact congrArg q uv
    · exact (tests v u vu ((iff v u).mp eq.symm)).elim

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_noncentral_level_embedding_test
