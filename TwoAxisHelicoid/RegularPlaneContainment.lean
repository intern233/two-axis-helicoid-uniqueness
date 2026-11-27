import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Connected.Clopen

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff

/-- If a regular surface has closed image and lies in a parameterized
plane with a smooth ambient left inverse, it covers the whole plane.
The rank argument is local and allows different parameter points to
represent the same surface point. -/
theorem regular_image_eq_parameterized_plane {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set ℂ} (hU : IsOpen U) (hn : U.Nonempty) (X : ℂ → V)
    (hX : ∀ z ∈ U, ContDiffAt ℝ 1 X z)
    (hiX : ∀ z ∈ U, Function.Injective (fderiv ℝ X z)) (hclosed : IsClosed (X '' U))
    (i : ℂ → V) (j : V → ℂ) (hi : ContDiff ℝ 1 i) (hj : ContDiff ℝ 1 j)
    (hji : Function.LeftInverse j i) (hsub : X '' U ⊆ range i) : X '' U = range i := by
  let f := j ∘ X
  have recovers (z : ℂ) (hz : z ∈ U) : i (f z) = X z := by
    obtain ⟨v,hv⟩ := hsub (mem_image_of_mem X hz)
    change i (j (X z)) = X z
    rw [← hv,hji v]
  have hset : f '' U = i ⁻¹' (X '' U) := by
    ext z
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u,hu,(recovers u hu).symm⟩
    · rintro ⟨u,hu,he⟩
      exact ⟨u,hu,(congrArg j he).trans (hji z)⟩
  have hc : IsClosed (f '' U) := hset ▸ hclosed.preimage hi.continuous
  have ho : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z,hz,rfl⟩
    have hf : ContDiffAt ℝ 1 f z := hj.contDiffAt.comp z (hX z hz)
    have germ : i ∘ f =ᶠ[𝓝 z] X := by
      filter_upwards [hU.mem_nhds hz] with w hw using recovers w hw
    have comp := (hi.differentiable one_ne_zero (f z)).hasFDerivAt.comp z (hf.differentiableAt one_ne_zero).hasFDerivAt
    have der : fderiv ℝ X z = (fderiv ℝ i (f z)).comp (fderiv ℝ f z) := germ.fderiv_eq.symm.trans comp.fderiv
    have inj : Function.Injective (fderiv ℝ f z) := by
      intro a b he
      apply hiX z hz
      rw [der]
      exact congrArg (fderiv ℝ i (f z)) he
    have sur : Function.Surjective (fderiv ℝ f z) :=
      (LinearMap.injective_iff_surjective (f := (fderiv ℝ f z).toLinearMap)).mp inj
    rw [← (hf.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr sur)]
    exact Filter.image_mem_map (hU.mem_nhds hz)
  have all := (show IsClopen (f '' U) from ⟨hc,ho⟩).eq_univ (hn.image f)
  apply Subset.antisymm hsub
  rintro _ ⟨w,rfl⟩
  have hw : w ∈ f '' U := all ▸ mem_univ w
  obtain ⟨z,hz,rfl⟩ := hw
  exact ⟨z,hz,(recovers z hz).symm⟩

/-- A regular surface with connected analytic chart domain and closed
image, which locally lies in an analytically defined plane, has the
entire image of that plane. -/
theorem analytically_contained_regular_surface_image {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U) {z : ℂ} (hz : z ∈ U)
    (X : ℂ → V) (hX : AnalyticOnNhd ℝ X U)
    (hinj : ∀ w ∈ U, Function.Injective (fderiv ℝ X w)) (hclosed : IsClosed (X '' U))
    (i : ℂ → V) (j : V → ℂ) (hi : ContDiff ℝ 1 i) (hj : ContDiff ℝ 1 j)
    (hji : Function.LeftInverse j i) (s : V → ℝ) (hs : ∀ p, AnalyticAt ℝ s p)
    (hzero : ∀ p, s p = 0 ↔ p ∈ range i) (hgerm : ∀ᶠ w in 𝓝 z, X w ∈ range i) :
    X '' U = range i := by
  have hof : AnalyticOnNhd ℝ (s ∘ X) U := fun w hw => (hs _).comp (hX w hw)
  have hnear : (s ∘ X) =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [hgerm] with w hw using (hzero _).mpr hw
  have hall := hof.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hz hnear
  apply regular_image_eq_parameterized_plane hU ⟨z,hz⟩ X (fun w hw => (hX w hw).contDiffAt)
    hinj hclosed i j hi hj hji
  rintro _ ⟨w,hw,rfl⟩
  exact (hzero _).mp (hall hw)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_image_eq_parameterized_plane

#print axioms TwoAxisHelicoid.analytically_contained_regular_surface_image
