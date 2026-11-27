import TwoAxisHelicoid.SolidTorusBoundaryCoordinates
import TwoAxisHelicoid.SmoothExtensionClosedGerms
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped ContDiff

abbrev solidParameterCylinder : Set (ℝ × ℂ) := univ ×ˢ closedBall 0 1

/-- The standard meaning of a smooth regular parametrization on a closed
solid torus: near each finite point it has a smooth regular ambient extension
from the closed parameter domain. No single extension or collar is supplied. -/
def SmoothFiniteSolidGerms (S : Circle × ℂ → OnePoint (Fin 3 → ℝ)) : Prop :=
  ∀ a : Circle, ∀ x ∈ solidParameterCylinder, S (Circle.exp x.1*a,x.2) ≠ OnePoint.infty →
    ∃ (U : Set (ℝ × ℂ)) (g : ℝ × ℂ → Fin 3 → ℝ), IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
      Function.Injective (fderiv ℝ g x) ∧
      ∀ w ∈ U ∩ solidParameterCylinder, (g w : OnePoint (Fin 3 → ℝ)) = S (Circle.exp w.1*a,w.2)

/-- Compactness of a meridian disk missing infinity gives a uniform
longitudinal interval on which every point remains in the finite chart. -/
theorem finite_meridian_longitude_interval (S : Circle × ℂ → OnePoint (Fin 3 → ℝ))
    (hS : ContinuousOn S (univ ×ˢ closedBall 0 1)) (a : Circle)
    (hfinite : ∀ z ∈ closedBall (0:ℂ) 1, S (a,z) ≠ OnePoint.infty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (-δ) δ, ∀ z ∈ closedBall (0:ℂ) 1, S (Circle.exp s*a,z) ≠ OnePoint.infty := by
  let T (w : ℝ × MeridianDiskParameter) := S (Circle.exp w.1*a,w.2.1)
  have hc : Continuous T := hS.comp_continuous (((Circle.exp.continuous.comp continuous_fst).mul continuous_const).prodMk
    (continuous_subtype_val.comp continuous_snd)) (fun w => ⟨trivial,w.2.2⟩)
  let N := {w : ℝ × MeridianDiskParameter | T w ≠ OnePoint.infty}
  have hN : IsOpen N := isOpen_ne_fun hc continuous_const
  let _ : CompactSpace MeridianDiskParameter := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
  have hsub : ({0} : Set ℝ) ×ˢ (univ : Set MeridianDiskParameter) ⊆ N := by
    rintro ⟨s,z⟩ ⟨hs,_⟩
    have h0 : s = 0 := hs
    simpa [N,T,h0] using hfinite z.1 z.2
  obtain ⟨U,V,hU,_,h0,huv,hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := (0:ℝ))) isCompact_univ hN hsub
  obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0 (mem_singleton _)))
  refine ⟨r/2,half_pos hr,fun s hs z hz => ?_⟩
  have hsb : s ∈ ball (0:ℝ) r := by
    rw [mem_ball,Real.dist_eq,sub_zero,abs_lt]
    constructor <;> linarith [hs.1,hs.2]
  exact hUV (show (s,(⟨z,hz⟩ : MeridianDiskParameter)) ∈ U ×ˢ V from ⟨hb hsb,huv trivial⟩)

/-- Glue local smooth meridional germs throughout a whole closed disk.
At its circular boundary, uniqueness of derivatives on the solid cylinder
preserves the rank of each local derivative. -/
theorem relative_meridian_has_smooth_chart (S : Circle × ℂ → OnePoint (Fin 3 → ℝ))
    (hS : ContinuousOn S (univ ×ˢ closedBall 0 1)) (hsm : SmoothFiniteSolidGerms S) (a : Circle)
    (hfinite : ∀ z ∈ closedBall (0:ℂ) 1, S (a,z) ≠ OnePoint.infty) :
    ∃ (δ : ℝ) (G : ℝ × ℂ → Fin 3 → ℝ), 0 < δ ∧ ContDiff ℝ ∞ G ∧
      (∀ z ∈ closedBall (0:ℂ) 1, Function.Injective (fderiv ℝ G (0,z))) ∧
      ∀ s ∈ Icc (-δ) δ, ∀ z ∈ closedBall (0:ℂ) 1, (G (s,z) : OnePoint (Fin 3 → ℝ)) = S (Circle.exp s*a,z) := by
  obtain ⟨δ,hδ,hfin⟩ := finite_meridian_longitude_interval S hS a hfinite
  let K := Icc (-δ) δ ×ˢ closedBall (0:ℂ) 1
  let f (w : ℝ × ℂ) := (S (Circle.exp w.1*a,w.2)).elim 0 id
  have hKC : K ⊆ solidParameterCylinder := fun w hw => ⟨trivial,hw.2⟩
  have hgerm (x : ℝ × ℂ) (hx : x ∈ K) := hsm a x (hKC hx) (hfin x.1 hx.1 x.2 hx.2)
  obtain ⟨G,hG,he⟩ := smooth_extension_from_closed_germs K (isClosed_Icc.prod isClosed_closedBall) f (by
    intro x hx
    obtain ⟨U,g,hU,hxU,hg,_,hge⟩ := hgerm x hx
    refine ⟨U,g,hU,hxU,hg,fun w hw => ?_⟩
    simpa [f] using congrArg (fun y : OnePoint (Fin 3 → ℝ) => y.elim 0 id) (hge w ⟨hw.1,hKC hw.2⟩))
  have huniq : UniqueDiffOn ℝ K := (uniqueDiffOn_Icc (by linarith : -δ < δ)).prod
    (uniqueDiffOn_convex (convex_closedBall (0:ℂ) 1) (by rw [interior_closedBall _ one_ne_zero]; exact ⟨0,mem_ball_self zero_lt_one⟩))
  refine ⟨δ,G,hδ,hG,fun z hz => ?_,fun s hs z hz => ?_⟩
  · let x := ((0:ℝ),z)
    have hx : x ∈ K := ⟨⟨(neg_lt_zero.mpr hδ).le,hδ.le⟩,hz⟩
    obtain ⟨U,g,hU,hxU,hg,hgi,hge⟩ := hgerm x hx
    have hEq : G =ᶠ[𝓝[K] x] g := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)] with w hw hu
      rw [he hw]
      exact (congrArg (fun y : OnePoint (Fin 3 → ℝ) => y.elim 0 id) (hge w ⟨hu,hKC hw⟩)).symm
    have h0 := (hg.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hd : fderiv ℝ G x = fderiv ℝ g x := (huniq x hx).eq
      (hG.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
      (h0.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq hEq (hEq.eq_of_nhdsWithin hx))
    exact hd ▸ hgi
  · rw [he (show (s,z) ∈ K from ⟨hs,hz⟩)]
    obtain ⟨w,hw⟩ := OnePoint.ne_infty_iff_exists.mp (hfin s hs z hz)
    change (↑((S (Circle.exp s*a,z)).elim (0 : Fin 3 → ℝ) id) : OnePoint (Fin 3 → ℝ)) = _
    rw [← hw]; rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.relative_meridian_has_smooth_chart
