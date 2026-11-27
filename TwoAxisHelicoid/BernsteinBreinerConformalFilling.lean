import TwoAxisHelicoid.CompactConformalDoublePoleEnd
import TwoAxisHelicoid.AbstractPuncturedConformalFilling

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology OnePoint Manifold ContDiff

/-- The compact Riemann surface, conformal puncturing and two
meromorphic double poles of Bernstein--Breiner Theorem 1.1, in
an arbitrary compact model, furnish the local end data needed for
the marked-torus reduction of the actual original surface. -/
theorem abstract_conformal_filling_gives_double_pole_end
    {M N : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    [TopologicalSpace N] [T2Space N] [CompactSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ,ℂ) ω N]
    (b : M) (p : N) (j : M ≃ₜ {q : N // q ≠ p})
    (hj : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x => (j x).1))
    (χ : OpenPartialHomeomorph N ℂ) (hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N)
    (hp : p ∈ χ.source) (h0 : χ p = 0)
    (X : M → Fin 3 → ℝ) (Z : N → Fin 3 → ℝ) (hZ : ∀ x, Z (j x).1 = X x)
    (hh : MeromorphicAt (fun z => immersionComplexCoefficient (Z ∘ χ.symm) z 2) 0)
    (hho : meromorphicOrderAt (fun z => immersionComplexCoefficient (Z ∘ χ.symm) z 2) 0 = -2)
    (hg : MeromorphicAt (immersionGaussLogDerivative (Z ∘ χ.symm)) 0)
    (hgo : meromorphicOrderAt (immersionGaussLogDerivative (Z ∘ χ.symm)) 0 = -2) :
    Nonempty (GeometricDoublePoleEnd X) := by
  obtain ⟨S,hm,D,hDx,hinf,hinc⟩ := abstract_punctured_conformal_filling p j hj
  let _ := S
  have hman : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := hm
  let d := D.toHomeomorph.toOpenPartialHomeomorph.trans χ
  have hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint M) := by
    apply d.mem_maximalAtlas_of_contMDiffOn
    · intro q hq
      exact ((contMDiffAt_of_mem_maximalAtlas hχ hq.2).comp q D.contMDiff.contMDiffAt).contMDiffWithinAt
    · intro w hw
      exact (D.symm.contMDiff.contMDiffAt.comp w (contMDiffAt_symm_of_mem_maximalAtlas hχ hw.1)).contMDiffWithinAt
  have hmem : D OnePoint.infty ∈ χ.source := hinf.symm ▸ hp
  have hs0 : OnePoint.infty ∈ d.source := ⟨mem_univ _,hmem⟩
  have hdz : d OnePoint.infty = 0 := (congrArg χ hinf).trans h0
  let V := (fun q : OnePoint M => q.elim 0 X) ∘ d.symm
  have he : V =ᶠ[𝓝[≠] (0:ℂ)] Z ∘ χ.symm := by
    have ht : (0:ℂ) ∈ χ.target := h0 ▸ χ.map_source hp
    filter_upwards [nhdsWithin_le_nhds (χ.open_target.mem_nhds ht),self_mem_nhdsWithin] with w hw hn
    have hwp : χ.symm w ≠ p := fun h => hn ((χ.right_inv hw).symm.trans ((congrArg χ h).trans h0))
    let a : {q : N // q ≠ p} := ⟨χ.symm w,hwp⟩
    let x := j.symm a
    have hx : (j x).1 = χ.symm w := congrArg Subtype.val (j.apply_symm_apply a)
    have hx' : D.symm (χ.symm w) = (x:OnePoint M) := D.toHomeomorph.symm_apply_eq.mpr ((hDx x).trans hx).symm
    change (D.symm (χ.symm w)).elim 0 X = Z (χ.symm w)
    rw [hx',← hx]
    exact (hZ x).symm
  obtain ⟨hcoeff,hlog⟩ := spatial_equal_germ_end_coefficients he
  have hheight := hcoeff.fun_comp (fun A => A 2)
  exact conformal_filling_actual_double_pole_end b hinc d hd hs0 hdz X
    (hh.congr hheight.symm) ((meromorphicOrderAt_congr hheight).trans hho)
    (hg.congr hlog.symm) ((meromorphicOrderAt_congr hlog).trans hgo)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.abstract_conformal_filling_gives_double_pole_end
