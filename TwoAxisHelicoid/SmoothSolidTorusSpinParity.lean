import TwoAxisHelicoid.PuncturedCompressingDiskParity
import TwoAxisHelicoid.SolidTorusMeridianDisk
import TwoAxisHelicoid.SolidMeridianRelativeExtension

namespace TwoAxisHelicoid
open Complex Set Metric Topology
open scoped Manifold ContDiff

/-- A smooth solid torus in the one-point compactification of Euclidean
three-space, specified in actual longitude and complex disk coordinates.
Only the closed solid is required to be injectively parametrized, and
its smooth finite spatial charts are given by germs on the closed solid.
No spin, Arf or compression-disk assertion is part of these data. -/
def HasSmoothCompactifiedSolidTorus {M : Type*} (F : M → Fin 3 → ℝ) : Prop :=
  ∃ S : Circle × ℂ → OnePoint (Fin 3 → ℝ),
    ContinuousOn S (univ ×ˢ closedBall 0 1) ∧ InjOn S (univ ×ˢ closedBall 0 1) ∧
    range (fun v : Circle × Circle => S (v.1,(v.2 : ℂ))) = range (fun p => (F p : OnePoint (Fin 3 → ℝ))) ∧
    SmoothFiniteSolidGerms S

/-- The outward solid side may contain spatial infinity. A meridian disk
avoiding infinity and the capped point is selected from the genuine product
and yields even Arf parity of the actual Euclidean tangent-adapted frames. -/
theorem compactified_solid_torus_forces_even_arf (L : PeriodPair) {F : PeriodTorus L → Fin 3 → ℝ}
    (hF : IsEmbedding F)
    (hs : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (hi : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (hsolid : HasSmoothCompactifiedSolidTorus F) :
    capAmbientSpinQuadratic L F (1,0) * capAmbientSpinQuadratic L F (0,1) = 0 := by
  obtain ⟨S,hS,hSi,hSbd,hreg⟩ := hsolid
  obtain ⟨H,hH⟩ := solid_torus_compactified_boundary_marking L F hF S hS hSi hSbd
  let B (v : Circle × MeridianDiskParameter) := S (v.1,v.2.1)
  have hB : Function.Injective B := by
    intro x y h
    have he : (x.1,x.2.1)=(y.1,y.2.1) := hSi ⟨trivial,x.2.2⟩ ⟨trivial,y.2.2⟩ h
    exact Prod.ext (congrArg (Prod.fst : Circle × ℂ → Circle) he) (Subtype.ext (congrArg (Prod.snd : Circle × ℂ → ℂ) he))
  obtain ⟨a,ha,havoid⟩ := solid_torus_has_meridian_avoiding_finite B hB {OnePoint.infty} (finite_singleton _)
    {(H.symm 0).1} (finite_singleton _)
  have ha0 (u : Circle) : H (a,u) ≠ 0 := by
    intro hz
    apply ha
    exact congrArg Prod.fst ((H.symm_apply_apply (a,u)).symm.trans (congrArg H.symm hz))
  obtain ⟨δ,E,hδ,hE,hEi,hmatch⟩ := relative_meridian_has_smooth_chart S hS hreg a
    (fun z hz => havoid ⟨z,hz⟩)
  have hb (s : ℝ) (hsδ : s ∈ Ioo (-δ) δ) (u : Circle) : F (H (Circle.exp s*a,u)) = E (s,(u:ℂ)) := by
    apply OnePoint.coe_injective
    exact (hH _ _).trans (hmatch s ⟨hsδ.1.le,hsδ.2.le⟩ u (by simp [mem_closedBall])).symm
  obtain ⟨ξ,period,hξ,hx,hω,hωL,hper,hr,hinj,hG,hGD,hGi,hbd,htr⟩ :=
    solid_torus_meridian_disk_data L hs hi H a ha0 E (fun _ _ => hE.contDiffAt) hEi hδ hb
  exact punctured_marked_torus_with_compressing_disk_even L hs hi hξ hx hω hωL hper hr hinj hG hGD hGi hbd htr

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactified_solid_torus_forces_even_arf
