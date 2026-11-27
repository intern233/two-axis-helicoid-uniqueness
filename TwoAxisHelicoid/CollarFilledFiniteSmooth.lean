import TwoAxisHelicoid.CollarFilledAnalyticAtlas

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

theorem curve_map_real_smooth_at_of_holomorphic {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N] {f : M → N} {x : M}
    (h : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f x) : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f x := by
  obtain ⟨hc,hd⟩ := contMDiffAt_iff.mp h
  refine contMDiffAt_iff.mpr ⟨hc,?_⟩
  simpa only [mfld_simps] using! (hd.restrict_scalars ℝ).of_le (show (∞ : WithTop ℕ∞)≤ω by simp)

private theorem finite_chart_inclusion_and_inverse {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [ChartedSpace ℂ (OnePoint M)] [IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M)]
    (e : OpenPartialHomeomorph M ℂ) (a : OpenPartialHomeomorph (OnePoint M) ℂ)
    (ca : a∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint M))
    (matchChart : ∀ x∈e.source, (x:OnePoint M)∈a.source ∧ a (x:OnePoint M)=e x)
    {x : M} (hx : x∈e.source)
    (fe : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ e x)
    (be : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ e.symm (e x)) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (OnePoint.some : M → OnePoint M) x ∧
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (fun p : OnePoint M => p.elim x id) (x:OnePoint M) := by
  obtain ⟨ax,eqn⟩ := matchChart x hx
  have ba := curve_map_real_smooth_at_of_holomorphic (contMDiffAt_symm_of_mem_maximalAtlas ca (eqn ▸ a.map_source ax))
  have fa := curve_map_real_smooth_at_of_holomorphic (contMDiffAt_of_mem_maximalAtlas ca ax)
  constructor
  · apply (ba.comp x fe).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    obtain ⟨ay,agrees⟩ := matchChart y hy
    exact (a.left_inv ay).symm.trans (congrArg a.symm agrees)
  · have inv : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ e.symm (a (x:OnePoint M)) := eqn.symm ▸ be
    apply (inv.comp (x:OnePoint M) fa).congr_of_eventuallyEq
    rw [Filter.EventuallyEq,OnePoint.nhds_coe_eq,Filter.eventually_map]
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    change y=e.symm (a (y:OnePoint M))
    rw [(matchChart y hy).2,e.left_inv hy]

theorem collarFilledAtlas_real_finite_points {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] (E : PuncturedComplexEnd M)
    (U : Set M) (op : IsOpen U) (cover : ∀ x : M, x∈U ∨ x∈E.coord.source)
    (man : let _ := collarFilledAtlas E U op cover; IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M))
    (fw : ∀ x∈E.coord.source, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ E.coord x)
    (bw : ∀ w∈E.coord.target, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ E.coord.symm w) :
    let _ := collarFilledAtlas E U op cover
    ∀ x : M, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (OnePoint.some : M → OnePoint M) x ∧
      ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (fun p : OnePoint M => p.elim x id) (x:OnePoint M) := by
  let _ := collarFilledAtlas E U op cover
  let _ : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := man
  change ∀ x : M, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (OnePoint.some : M → OnePoint M) x ∧
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (fun p : OnePoint M => p.elim x id) (x:OnePoint M)
  intro x
  rcases cover x with hu|he
  · let b := (chartAt ℂ x).restr U
    have bm : b∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M :=
      restr_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ,ℂ)) (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)) op
    have shape : b.source=(chartAt ℂ x).source∩U := (chartAt ℂ x).restr_source' U op
    have bx : x∈b.source := shape ▸ ⟨mem_chart_source ℂ x,hu⟩
    have bs : b.source⊆U := shape ▸ inter_subset_right
    have atlas : finiteOnePointChart b∈atlas ℂ (OnePoint M) := Or.inl ⟨b,bm,bs,rfl⟩
    exact finite_chart_inclusion_and_inverse b (finiteOnePointChart b) (IsManifold.subset_maximalAtlas atlas)
      (fun y h => ⟨(finiteOnePointChart_coe_source b y).mpr h,rfl⟩) bx
      (curve_map_real_smooth_at_of_holomorphic (contMDiffAt_of_mem_maximalAtlas bm bx))
      (curve_map_real_smooth_at_of_holomorphic (contMDiffAt_symm_of_mem_maximalAtlas bm (b.map_source bx)))
  · have atlas : E.filledChart∈atlas ℂ (OnePoint M) := Or.inr rfl
    exact finite_chart_inclusion_and_inverse E.coord E.filledChart (IsManifold.subset_maximalAtlas atlas)
      (fun y h => ⟨(compactifiedEndChart_coe_source E y).mpr h,rfl⟩) he (fw x he) (bw _ (E.coord.map_source he))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.collarFilledAtlas_real_finite_points

