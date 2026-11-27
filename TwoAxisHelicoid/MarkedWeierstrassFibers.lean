import TwoAxisHelicoid.AnalyticSecondOrderUniqueness
import TwoAxisHelicoid.WeierstrassSecondOrder
import TwoAxisHelicoid.WeierstrassSurjectivity
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- The second-order Weierstrass equation on the entire complement of
any complex lattice, including its ramification points. -/
theorem marked_weierstrass_second_order (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice) :
    deriv L.derivWeierstrassP w = 6*L.weierstrassP w^2-L.g₂/2 := by
  have cnt : (L.lattice:Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  have conn := (cnt.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ)).isPreconnected
  have some : ∃ z ∉ L.lattice, L.derivWeierstrassP z ≠ 0 := by
    by_contra! he
    obtain ⟨a,ha,ea⟩ := weierstrassP_attains_every_finite_value L 0
    obtain ⟨b,hb,eb⟩ := weierstrassP_attains_every_finite_value L 1
    have eq := L.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero conn
      L.analyticOnNhd_weierstrassP.differentiableOn
      (fun z hz => (congrFun L.deriv_weierstrassP z).trans (he z hz)) ha hb
    exact zero_ne_one (ea.symm.trans (eq.trans eb))
  obtain ⟨z,hz,hn⟩ := some
  have right : AnalyticOnNhd ℂ (fun u => 6*L.weierstrassP u^2-L.g₂/2) (L.lattice:Set ℂ)ᶜ :=
    fun u hu => (analyticAt_const.mul ((L.analyticOnNhd_weierstrassP u hu).pow 2)).sub analyticAt_const
  apply L.analyticOnNhd_derivWeierstrassP.deriv.eqOn_of_preconnected_of_eventuallyEq right conn hz _ hw
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,
    (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt.eventually_ne hn] with u hu hd
  exact weierstrass_second_order_of_noncritical L hu hd

/-- The value and derivative of ℘ determine the point modulo the lattice.
The period conclusion follows from the genuine double pole after analytic
continuation of the two translated solutions of the Weierstrass ODE. -/
theorem marked_weierstrass_value_derivative_injective (L : PeriodPair) {a b : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hv : L.weierstrassP a = L.weierstrassP b)
    (hd : L.derivWeierstrassP a = L.derivWeierstrassP b) : b-a ∈ L.lattice := by
  by_contra hn
  let δ := b-a
  let T := fun w : ℂ => w+δ
  let f := L.weierstrassP
  let q := fun w => f (w+δ)
  let U := ((L.lattice:Set ℂ) ∪ T ⁻¹' (L.lattice:Set ℂ))ᶜ
  have cT : Continuous T := continuous_id.add continuous_const
  have op : IsOpen U := (L.isClosed_lattice.union (L.isClosed_lattice.preimage cT)).isOpen_compl
  have count : (L.lattice:Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  have conn : IsPreconnected U := ((count.union (count.preimage (f := T) (fun _ _ he => add_right_cancel he))).isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ)).isPreconnected
  have eqb : a+δ = b := by dsimp [δ]; abel
  have haU : a ∈ U := fun h => h.elim ha (fun e => hb (eqb ▸ e))
  have hleft : AnalyticOnNhd ℂ f U := fun w hw => L.analyticOnNhd_weierstrassP _ (fun h => hw (Or.inl h))
  have hright : AnalyticOnNhd ℂ q U := fun w hw =>
    (L.analyticOnNhd_weierstrassP _ (fun h => hw (Or.inr h))).comp (analyticAt_id.add analyticAt_const)
  have d1 : deriv q = fun w => L.derivWeierstrassP (w+δ) := by
    funext w
    exact (deriv_comp_add_const f δ w).trans (congrFun L.deriv_weierstrassP _)
  have eqreg : f =ᶠ[𝓝 a] q := by
    apply analytic_quadratic_ode_germ_unique (A := 6) (B := -L.g₂/2) (hleft _ haU) (hright _ haU)
    · filter_upwards [op.mem_nhds haU] with w hw
      dsimp only [f]
      rw [L.deriv_weierstrassP,marked_weierstrass_second_order L (fun h => hw (Or.inl h))]
      ring
    · filter_upwards [op.mem_nhds haU] with w hw
      rw [d1,deriv_comp_add_const,marked_weierstrass_second_order L (fun h => hw (Or.inr h))]
      dsimp [q,f]
      ring
    · simpa only [f,q,eqb] using hv
    · rw [d1]
      simpa only [f,L.deriv_weierstrassP,eqb] using hd
  have eqU := hleft.eqOn_of_preconnected_of_eventuallyEq hright conn haU eqreg
  have out : T 0 ∉ L.lattice := by simpa [T,δ] using hn
  have near : f =ᶠ[𝓝[≠] (0:ℂ)] q := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin,nhdsWithin_le_nhds (cT.continuousAt (L.isClosed_lattice.isOpen_compl.mem_nhds out))] with w hw hne ht
    exact eqU (fun e => e.elim (fun h => hw ⟨h,hne⟩) ht)
  have hreg : AnalyticAt ℂ q 0 :=
    (L.analyticOnNhd_weierstrassP _ out).comp (analyticAt_id.add analyticAt_const)
  have ho := meromorphicOrderAt_congr near
  rw [show meromorphicOrderAt f 0 = -2 from L.order_weierstrassP 0 L.lattice.zero_mem] at ho
  have hpos := hreg.meromorphicOrderAt_nonneg
  rw [← ho] at hpos
  exact (by decide : ¬ (0 : WithTop ℤ) ≤ -2) hpos

/-- A critical point is the only point of its ℘-fiber on an arbitrary
marked torus. In particular, two inequivalent zeros of an elliptic height
coefficient A ℘ + B must both be simple. -/
theorem marked_weierstrass_regular_of_distinct_fiber_points (L : PeriodPair) {a b : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hv : L.weierstrassP a = L.weierstrassP b)
    (hne : b-a ∉ L.lattice) : L.derivWeierstrassP a ≠ 0 := by
  intro he
  have eq : L.derivWeierstrassP b ^ 2 = L.derivWeierstrassP a ^ 2 := by
    rw [L.derivWeierstrassP_sq a ha,L.derivWeierstrassP_sq b hb,hv]
  have hb' : L.derivWeierstrassP b = 0 := by simpa [he] using eq
  exact hne (marked_weierstrass_value_derivative_injective L ha hb hv (he.trans hb'.symm))

/-- The two points over a finite regular value differ precisely by the
elliptic involution. -/
theorem marked_weierstrass_fiber_iff (L : PeriodPair) {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) :
    L.weierstrassP a = L.weierstrassP b ↔ b-a ∈ L.lattice ∨ b+a ∈ L.lattice := by
  constructor
  · intro hv
    have e : L.derivWeierstrassP a ^ 2 = L.derivWeierstrassP b ^ 2 := by
      rw [L.derivWeierstrassP_sq a ha,L.derivWeierstrassP_sq b hb,hv]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with eq|eq
    · exact Or.inl (marked_weierstrass_value_derivative_injective L ha hb hv eq)
    · apply Or.inr
      simpa using marked_weierstrass_value_derivative_injective L (a := -a) (by simpa using ha) hb
        ((L.weierstrassP_neg a).trans hv) (by rw [L.derivWeierstrassP_neg,eq,neg_neg])
  · rintro (h|h)
    · simpa using (L.weierstrassP_add_coe a (⟨b-a,h⟩ : L.lattice)).symm
    · simpa using (L.weierstrassP_add_coe (-a) (⟨b+a,h⟩ : L.lattice)).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_weierstrass_fiber_iff
#print axioms TwoAxisHelicoid.marked_weierstrass_regular_of_distinct_fiber_points
