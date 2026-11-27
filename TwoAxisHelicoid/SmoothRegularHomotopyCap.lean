import TwoAxisHelicoid.RegularHomotopyGeneratorParity
import TwoAxisHelicoid.RegularHomotopySpaceDerivative
import TwoAxisHelicoid.MultiplierCanonicalSquare
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Manifold ContDiff

theorem period_torus_projection_real_smooth (L : PeriodPair) (z : ℂ) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (periodTorusProjection L) z := by
  obtain ⟨period,hω⟩ := period_torus_projection_chart_translate L z
  have hd : ContDiffAt ℝ ∞ (chartAt ℂ (periodTorusProjection L z) ∘ periodTorusProjection L) z :=
    (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq hω
  apply contMDiffAt_iff.mpr
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt,?_⟩
  simpa only [writtenInExtChartAt,mfld_simps,contDiffWithinAt_univ] using! hd

variable (L : PeriodPair) [cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L)]
include cs

/-- Regularity of a spatial map survives a change between the actual cap
atlas and the original marked atlas where the identity is a local smooth
diffeomorphism. This uses the chain rule in both directions. -/
theorem cap_smooth_map_marked_regular (G : PeriodTorus L → Fin 3 → ℝ) {q : PeriodTorus L}
    (hg : ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ G q)
    (hgi : Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) G q))
    (ha : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus L)) q)
    (hb : ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus L)) q) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ G q ∧ Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) G q) := by
  let a := mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) (@id (PeriodTorus L)) q
  let b := mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) (@id (PeriodTorus L)) q
  have hid : b.comp a = ContinuousLinearMap.id ℝ _ := by
    exact (mfderiv_comp q (hb.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))).symm.trans
      (show mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (@id (PeriodTorus L)) q = _ from mfderiv_id)
  have hai : Function.Injective a := by
    intro x y h
    have hx := DFunLike.congr_fun hid x
    have hy := DFunLike.congr_fun hid y
    exact hx.symm.trans ((congrArg b h).trans hy)
  refine ⟨hg.comp q ha,?_⟩
  have h := mfderiv_comp q (hg.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
  change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (G ∘ id) q)
  rw [h]
  exact hgi.comp hai


/-- In the closed-time-interval convention for smooth regular homotopies,
the actual Gram frames of both generators vary continuously in the
original punctured marking. No regularity of that marking at zero is used. -/
theorem compact_regular_homotopy_even_arf (H : ℝ × PeriodTorus L → Fin 3 → ℝ)
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ × ℝ)) 𝓘(ℝ,Fin 3 → ℝ) ∞ H (Icc (0:ℝ) 1 ×ˢ univ))
    (hS : ∀ (s : unitInterval) q, ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (fun p => H (s.1,p)) q)
    (hI : ∀ (s : unitInterval) q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) (fun p => H (s.1,p)) q))
    (hA : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus L)) q ∧
      ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus L)) q)
    (he : capAmbientSpinQuadratic L (fun p => H (1,p)) (1,0) * capAmbientSpinQuadratic L (fun p => H (1,p)) (0,1) = 0) :
    capAmbientSpinQuadratic L (fun p => H (0,p)) (1,0) * capAmbientSpinQuadratic L (fun p => H (0,p)) (0,1) = 0 := by
  let F (s : unitInterval) (p : PeriodTorus L) := H (s.1,p)
  let U := ((L.lattice : Set ℂ)ᶜ)
  have hU : IsOpen U := L.isClosed_lattice.isOpen_compl
  have hπ : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) 1 (periodTorusProjection L) U := by
    intro z hz
    have hq : periodTorusProjection L z ≠ 0 := fun he => hz ((periodTorusProjection_eq_zero L z).mp he)
    exact (((hA _ hq).1.comp z (period_torus_projection_real_smooth L z)).of_le (by simp)).contMDiffWithinAt
  have hcs := (contMDiffOn_id (I := 𝓘(ℝ,ℝ)) (s := Icc (0:ℝ) 1)).prodMap hπ
  have ht := (hH.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp hcs (fun x hx => ⟨hx.1,trivial⟩)
  let Y (w : ℝ × ℂ) := H (w.1,periodTorusProjection L w.2)
  have hY : ContDiffOn ℝ 1 Y (Icc (0:ℝ) 1 ×ˢ U) := by
    rw [← contMDiffOn_iff_contDiffOn]
    rw [modelWithCornersSelf_prod,← chartedSpaceSelf_prod]
    exact ht
  have hc := interval_homotopy_spatial_derivative_continuous hU hY
  apply marked_arf_even_of_regular_homotopy L F _ _ he
  · intro i
    let γ : unitInterval → U := fun t => puncturedBasisLine L i t.1
    have hγ : Continuous γ := (puncturedBasisLine_continuous L i).comp continuous_subtype_val
    exact hc.comp (continuous_fst.prodMk (hγ.comp continuous_snd))
  · intro i w
    have hr (p : PeriodTorus L) (hp : p ≠ 0) := cap_smooth_map_marked_regular L (cs := cs) (F w.1)
      (hS w.1 p) (hI w.1 p) (hA p hp).1 (hA p hp).2
    exact (spatial_torus_lift_regular_at L (F w.1) (periodBasisLine_not_mem_lattice L i w.2.1)
      (fun p hp => (hr p hp).1) (fun p hp => (hr p hp).2)).2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_regular_homotopy_even_arf
