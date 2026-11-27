import TwoAxisHelicoid.HalfPeriodProduct
import TwoAxisHelicoid.PuncturedDiskPolygon
import Mathlib.Analysis.Analytic.Uniqueness

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A periodic meromorphic function on a marked torus cannot have a single
simple pole. The half-period argument works for every period lattice. -/
theorem elliptic_single_simple_pole_coefficient_zero (L : PeriodPair)
    {f g : ℂ → ℂ} {A : ℂ} (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z) (hg : AnalyticAt ℂ g 0)
    (hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z = A/z+g z) : A = 0 := by
  by_contra hA
  let h := L.ω₁ / 2
  let w := L.ω₂ / 2
  let D := halfFirstPeriodPair L
  let F := fun z => f z-g 0
  let G := fun z => g z-g 0
  have hF : AnalyticOnNhd ℂ F (L.lattice : Set ℂ)ᶜ :=
    fun z hz => (hf z hz).sub analyticAt_const
  have hG : AnalyticAt ℂ G 0 := hg.sub analyticAt_const
  have hper (z ω : ℂ) (hω : ω ∈ L.lattice) : F (z+ω) = F z := by
    simp only [F,hp z ω hω]
  have hlocal : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → F z = A/z+G z := by
    filter_upwards [hloc] with z hz hn
    simp only [F,G,hz hn,add_sub_assoc]
  have hh : F h = 0 := sub_eq_zero.mpr (elliptic_simple_pole_half_value L hf hp hg hloc
    L.ω₁_div_two_notMem_lattice (by convert L.ω₁_mem_lattice using 1; dsimp [h]; ring))
  have hw : F w = 0 := sub_eq_zero.mpr (elliptic_simple_pole_half_value L hf hp hg hloc
    L.ω₂_div_two_notMem_lattice (by convert L.ω₂_mem_lattice using 1; dsimp [w]; ring))
  obtain ⟨k,hk⟩ := elliptic_half_product_constant L hF hper hG hlocal hh
  have hkw := hk w D.ω₂_div_two_notMem_lattice
  rw [hw,zero_mul] at hkw
  have hnon : ∀ᶠ z in 𝓝 (0 : ℂ), A+z*G z ≠ 0 := by
    apply (continuousAt_const.add (continuousAt_id.mul hG.continuousAt)).eventually_ne
    simpa using hA
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → F z ≠ 0 ∧ z ∉ D.lattice := by
    filter_upwards [hnon,hlocal,D.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)] with z hn hl hD hz
    refine ⟨?_,fun hm => hD ⟨hm,hz⟩⟩
    rw [hl hz]
    intro he
    apply hn
    field_simp [hz] at he
    linear_combination he
  have halong : ∀ᶠ z in 𝓝 (0 : ℂ), F (z+h) = 0 := by
    filter_upwards [hnear] with z hz
    by_cases he : z=0
    · simpa only [he,zero_add] using hh
    · exact (mul_eq_zero.mp ((hk z (hz he).2).trans hkw.symm)).resolve_left (hz he).1
  have hshift : Tendsto (fun z : ℂ => z-h) (𝓝 h) (𝓝 0) := by
    simpa using (show Tendsto (fun z : ℂ => z) (𝓝 h) (𝓝 h) from tendsto_id).sub_const h
  have heq : F =ᶠ[𝓝 h] 0 := by
    filter_upwards [hshift.eventually halong] with z hz
    change F z = 0
    simpa only [sub_add_cancel] using hz
  have hcount : (L.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  have hconn := hcount.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ)
  have hevery := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn.isPreconnected
    L.ω₁_div_two_notMem_lattice heq
  obtain ⟨z,hz,hn⟩ := ((hnear.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ({0} : Set ℂ)ᶜ)).exists
  exact (hz hn).1 (hevery (fun hm => (hz hn).2 (lattice_le_halfFirstPeriodPair L hm)))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.elliptic_single_simple_pole_coefficient_zero
