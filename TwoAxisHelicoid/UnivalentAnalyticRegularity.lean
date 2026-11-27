import TwoAxisHelicoid.HolomorphicLocalWinding
import TwoAxisHelicoid.PlaneOrientationLocalConstancy
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.IsLocalHomeomorph

namespace TwoAxisHelicoid
open Complex Set Filter Function Topology Metric
open scoped Topology

/-- A univalent analytic map on an open plane domain has multiplicity
one at every point. The local topological winding counts the analytic order. -/
theorem univalent_analytic_deriv_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (op : IsOpen U)
    (an : AnalyticOnNhd ℂ f U) (inj : InjOn f U) {p : ℂ} (hp : p∈U) : deriv f p≠0 := by
  classical
  have non (x : ℂ) (hx : x∈U) : ¬ (∀ᶠ z in 𝓝 x, f z=f x) := by
    intro constant
    have h : ∀ᶠ z in 𝓝[≠] x, z≠x ∧ z∈U ∧ f z=f x := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (op.mem_nhds hx),
        constant.filter_mono nhdsWithin_le_nhds] with z hz hu eq using ⟨hz,hu,eq⟩
    obtain ⟨z,ne,hz,eq⟩ := h.exists
    exact ne (inj hz hx eq)
  have emb : IsOpenEmbedding (U.domRestrict f) := by
    apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    refine ⟨continuousOn_iff_continuous_domRestrict.mp an.continuousOn,inj.injective,?_⟩
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    change 𝓝 (f x.1)≤map (f ∘ (Subtype.val : U → ℂ)) (𝓝 x)
    rw [← map_map,op.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact (an x.1 x.2).eventually_constant_or_nhds_le_map_nhds.resolve_left (non x.1 x.2)
  have lh : IsLocalHomeomorphOn f U :=
    (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict U).mpr (fun x hx => ⟨U,op.mem_nhds hx,emb⟩)
  obtain ⟨e,src,fe⟩ := lh p hp
  obtain ⟨s,sign,orient⟩ := openPartialHomeomorph_orientation_sign e src
  have fo : HasPlaneOrientationAt f p s := fe ▸ orient
  let n := analyticOrderAt (fun z => f z-f p) p
  have fin : n≠⊤ := fun h => non p hp ((analyticOrderAt_eq_top.mp h).mono fun _ eq => sub_eq_zero.mp eq)
  obtain ⟨m,hm⟩ : ∃ m : ℕ, n=(m:ℕ∞) := ⟨n.toNat,(ENat.natCast_toNat_eq_self.mpr fin).symm⟩
  cases m with
  | zero => exact (((an p hp).sub analyticAt_const).analyticOrderAt_eq_zero.mp hm (sub_self _)).elim
  | succ k =>
    have wd := local_holomorphic_order_winding (OpenPartialHomeomorph.refl ℂ) (mem_univ p)
      (planeOrientation_identity p) (an p hp) hm
    have ord : (((k+1:ℕ):ℤ)*1)=s := wd.unique fo
    have kz : k=0 := by rcases sign with h|h <;> omega
    subst k
    have df := (an p hp).analyticOrderAt_deriv_add_one
    change analyticOrderAt (deriv f) p+1=n at df
    rw [hm] at df
    apply (an p hp).deriv.analyticOrderAt_eq_zero.mp
    exact (ENat.add_left_injective_of_ne_top (by decide : (1:ℕ∞)≠⊤)) (by simpa using df)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.univalent_analytic_deriv_ne_zero
