import TwoAxisHelicoid.PeriodTorusTopology
import TwoAxisHelicoid.RemovableGerms
import TwoAxisHelicoid.HarmonicComplexCoefficient
import TwoAxisHelicoid.PlanePolygonPrimitive

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A real period functional which annihilates a marked lattice vanishes
on the entire real plane. -/
theorem complex_eq_zero_of_lattice_real_periods (L : PeriodPair) {d : ℂ}
    (h : ∀ ω ∈ L.lattice, (ω*d).re = 0) : d = 0 := by
  let F := realCoefficientDerivative d
  have hle : Submodule.span ℝ (L.lattice : Set ℂ) ≤ LinearMap.ker F.toLinearMap :=
    Submodule.span_le.mpr (fun ω hω => h ω hω)
  rw [IsZLattice.span_top] at hle
  have h₁ : ((1:ℂ)*d).re = 0 := hle (show (1:ℂ) ∈ (⊤ : Submodule ℝ ℂ) from trivial)
  have h₂ : (I*d).re = 0 := hle (show I ∈ (⊤ : Submodule ℝ ℂ) from trivial)
  exact Complex.ext (by simpa using h₁) (by simpa using h₂)

theorem marked_torus_lattice_complement_connected (L : PeriodPair) :
    IsConnected (L.lattice : Set ℂ)ᶜ := by
  have hc : (L.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  exact hc.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ)

/-- Equality of the height differential follows from its removable
difference at the puncture and single-valuedness of the two true heights. -/
theorem torus_height_difference_of_removable_germ (L : PeriodPair) {p q : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p (L.lattice : Set ℂ)ᶜ) (hq : AnalyticOnNhd ℂ q (L.lattice : Set ℂ)ᶜ)
    {X Y : PeriodTorus L → ℝ}
    (hX : ∀ z ∉ L.lattice, HasFDerivAt (X ∘ periodTorusProjection L) (realCoefficientDerivative (p z)) z)
    (hY : ∀ z ∉ L.lattice, HasFDerivAt (Y ∘ periodTorusProjection L) (realCoefficientDerivative (q z)) z)
    (hper : ∀ z ω, ω ∈ L.lattice → z ∉ L.lattice → q (z+ω)-p (z+ω) = q z-p z)
    (hr : ∀ z ∈ L.lattice, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ (fun w => q w-p w) =ᶠ[𝓝[≠] z] g) :
    ∀ z ∉ L.lattice, q z = p z := by
  let U := (L.lattice : Set ℂ)ᶜ
  have hc : (L.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  have hshift (z ω : ℂ) (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) : z+ω ∉ L.lattice :=
    fun h => hz (by simpa using L.lattice.sub_mem h hω)
  obtain ⟨d,hd⟩ := elliptic_removable_germs_constant L hc hshift
    (fun z hz => (hq z hz).sub (hp z hz)) hper hr
  let V := (Y ∘ periodTorusProjection L)-(X ∘ periodTorusProjection L)
  have hv (z : ℂ) (hz : z ∈ U) : HasFDerivAt V (realCoefficientDerivative d) z := by
    convert (hY z hz).sub (hX z hz) using 1
    ext v
    change (v*d).re = (v*q z).re-(v*p z).re
    rw [← hd z hz,Pi.sub_apply,mul_sub,Complex.sub_re]
  obtain ⟨b,he⟩ := L.isClosed_lattice.isOpen_compl.exists_eq_add_of_fderiv_eq
    (marked_torus_lattice_complement_connected L).isPreconnected
    (fun z hz => (hv z hz).differentiableAt.differentiableWithinAt)
    (g := realCoefficientDerivative d) (fun _ _ => (realCoefficientDerivative d).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hv z hz).fderiv,(realCoefficientDerivative d).fderiv])
  obtain ⟨z,hz⟩ := (marked_torus_lattice_complement_connected L).nonempty
  have hd0 : d = 0 := by
    apply complex_eq_zero_of_lattice_real_periods L
    intro ω hω
    have h₁ := he hz
    have h₂ := he (hshift z ω hω hz)
    have eq : V (z+ω) = V z := by
      change Y (periodTorusProjection L (z+ω))-X (periodTorusProjection L (z+ω)) = _
      rw [periodTorusProjection_add_lattice L z ω hω]
      rfl
    change V z = (z*d).re + b at h₁
    change V (z+ω) = ((z+ω)*d).re + b at h₂
    rw [eq,add_mul,Complex.add_re] at h₂
    linarith
  exact fun z hz => sub_eq_zero.mp ((hd z hz).trans hd0)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_height_difference_of_removable_germ
