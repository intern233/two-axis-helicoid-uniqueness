import TwoAxisHelicoid.TorusHolomorphicLifts

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 1000000

/-- The removable extension uses one common value at every lattice point;
periodicity transports the local Laurent regular part at zero to all poles. -/
noncomputable def latticeRemovableExtension (L : PeriodPair) (f : ℂ → ℂ) (c : ℂ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ L.lattice then c else f z

theorem latticeRemovableExtension_periodic (L : PeriodPair) (f : ℂ → ℂ) (c : ℂ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω)=f z) (z ω : ℂ) (hω : ω ∈ L.lattice) :
    latticeRemovableExtension L f c (z+ω) = latticeRemovableExtension L f c z := by
  have hm : z+ω ∈ L.lattice ↔ z ∈ L.lattice := by
    constructor
    · intro h
      simpa only [add_sub_cancel_right] using L.lattice.sub_mem h hω
    · intro h
      exact L.lattice.add_mem h hω
  unfold latticeRemovableExtension
  rw [hm,hp z ω hω]

theorem latticeRemovableExtension_differentiable (L : PeriodPair) {f g : ℂ → ℂ}
    (hf : ∀ z ∉ L.lattice, DifferentiableAt ℂ f z)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω)=f z)
    (hg : AnalyticAt ℂ g 0)
    (hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z=g z) :
    Differentiable ℂ (latticeRemovableExtension L f (g 0)) := by
  have h0 : DifferentiableAt ℂ (latticeRemovableExtension L f (g 0)) 0 := by
    apply hg.differentiableAt.congr_of_eventuallyEq
    filter_upwards [hloc,L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)] with z hz hL
    unfold latticeRemovableExtension
    by_cases hm : z ∈ L.lattice
    · have he : z = 0 := by
        by_contra hn
        exact hL ⟨hm,hn⟩
      simp only [ite_eq_left hm,he]
    · rw [ite_eq_right hm]
      exact hz (by intro he; apply hm; rw [he]; exact L.lattice.zero_mem)
  intro z
  by_cases hz : z ∈ L.lattice
  · have hshift : DifferentiableAt ℂ
        (fun w : ℂ => latticeRemovableExtension L f (g 0) (w-z)) z := by
      have hzero : DifferentiableAt ℂ (latticeRemovableExtension L f (g 0)) (id z-z) := by
        simpa only [id_eq,sub_self] using h0
      have h := hzero.comp z (f := fun w : ℂ => w-z)
        (differentiableAt_id.sub_const z)
      simpa only [sub_self,Function.comp_def] using h
    have he : (fun w : ℂ => latticeRemovableExtension L f (g 0) (w-z)) =
        latticeRemovableExtension L f (g 0) := by
      funext w
      simpa only [sub_eq_add_neg] using
        latticeRemovableExtension_periodic L f (g 0) hp w (-z) (L.lattice.neg_mem hz)
    rwa [he] at hshift
  · apply (hf z hz).congr_of_eventuallyEq
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact ite_eq_right (show w ∉ L.lattice from hw)

/-- An elliptic function with a removable puncture is constant. The entire
extension is constructed inside the proof, so it is not a hypothesis. -/
theorem elliptic_removable_puncture_constant (L : PeriodPair) {f g : ℂ → ℂ}
    (hf : ∀ z ∉ L.lattice, DifferentiableAt ℂ f z)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω)=f z)
    (hg : AnalyticAt ℂ g 0)
    (hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z=g z) :
    ∀ z ∉ L.lattice, f z=g 0 := by
  have hd := latticeRemovableExtension_differentiable L hf hp hg hloc
  intro z hz
  have he := entire_lattice_periodic_constant L hd
    (latticeRemovableExtension_periodic L f (g 0) hp) z 0
  simpa only [latticeRemovableExtension,ite_eq_right hz,ite_eq_left L.lattice.zero_mem] using he

/-- Classification of the coefficient of a meromorphic differential on a
marked torus with its sole pole of order two and zero residue. The local
principal part is specified explicitly rather than by an arbitrary model
identification assumption. -/
theorem elliptic_double_pole_classification (L : PeriodPair) {f g : ℂ → ℂ} (A : ℂ)
    (hf : ∀ z ∉ L.lattice, DifferentiableAt ℂ f z)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω)=f z)
    (hg : AnalyticAt ℂ g 0)
    (hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z=A/z^2+g z) :
    ∀ z ∉ L.lattice, f z=A*L.weierstrassP z+g 0 := by
  have hwp (z : ℂ) : L.weierstrassP z = 1/z^2+L.weierstrassPExcept 0 z := by
    simpa only [Submodule.coe_zero,sub_zero,zero_pow (by decide : 2 ≠ 0),div_zero,add_comm] using
      (L.weierstrassPExcept_add (0 : L.lattice) z).symm
  have hreg : AnalyticAt ℂ (fun z => g z-A*L.weierstrassPExcept 0 z) 0 :=
    hg.sub (analyticAt_const.mul (L.analyticAt_weierstrassPExcept 0))
  have he := elliptic_removable_puncture_constant L
    (f := fun z => f z-A*L.weierstrassP z)
    (g := fun z => g z-A*L.weierstrassPExcept 0 z)
    (fun z hz => (hf z hz).sub (((L.analyticOnNhd_weierstrassP z hz).differentiableAt).const_mul A))
    (fun z ω hω => by rw [hp z ω hω,L.weierstrassP_add_coe z (⟨ω,hω⟩ : L.lattice)])
    hreg (by
      filter_upwards [hloc] with z hz hn
      rw [hz hn,hwp]
      ring)
  intro z hz
  have h := he z hz
  simp only [L.weierstrassPExcept_zero,mul_zero,sub_zero] at h
  linear_combination h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.elliptic_double_pole_classification
