import TwoAxisHelicoid.SlantedLattice
import TwoAxisHelicoid.RhombicLattice
import TwoAxisHelicoid.MarkedWeierstrassFibers
import TwoAxisHelicoid.EllipticPrincipalPart

namespace TwoAxisHelicoid
open Complex Set Filter Topology

/-- The rectangular sublattice used in the proof of Proposition 5.1 has
periods 2 and 2it. Its other coset in the rhombic lattice is 1+it. -/
noncomputable def manuscriptRectangularLattice (t : ℝ) (ht : 0<t) : PeriodPair :=
  rectangularPeriodPair (2*t) (by positivity)

theorem rectangular_lattice_le_rhombic {t : ℝ} (ht : 0<t) :
    (manuscriptRectangularLattice t ht).lattice≤(rhombicPeriodPair t ht).lattice := by
  intro z hz
  obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hz
  apply PeriodPair.mem_lattice.mpr
  refine ⟨m-n,2*n,?_⟩
  dsimp [manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair,rhombicPeriodPair]
  push_cast
  ring

theorem rectangular_lattice_and_coset {t : ℝ} (ht : 0<t) (z : ℂ) :
    z∈(rhombicPeriodPair t ht).lattice ↔ z∈(manuscriptRectangularLattice t ht).lattice ∨
      z-(1+I*t)∈(manuscriptRectangularLattice t ht).lattice := by
  let L := rhombicPeriodPair t ht
  let R := manuscriptRectangularLattice t ht
  let p : ℂ := 1+I*t
  have hp : p∈L.lattice := L.ω₂_mem_lattice
  have normal (m n k : ℤ) (parity : n=2*k ∨ n=2*k+1) :
      ((m:ℂ)*2+n*p)∈R.lattice ∨ (m*2+n*p)-p∈R.lattice := by
    rcases parity with he|he
    · apply Or.inl
      apply PeriodPair.mem_lattice.mpr
      refine ⟨m+k,k,?_⟩
      dsimp [R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair,p]
      rw [he]
      push_cast
      ring
    · apply Or.inr
      apply PeriodPair.mem_lattice.mpr
      refine ⟨m+k,k,?_⟩
      dsimp [R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair,p]
      rw [he]
      push_cast
      ring
  constructor
  · intro h
    obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp h
    exact normal m n (n/2) (by omega)
  · rintro (h|h)
    · exact rectangular_lattice_le_rhombic ht h
    · change z-p∈R.lattice at h
      have mem := L.lattice.add_mem (rectangular_lattice_le_rhombic ht h) hp
      simpa only [sub_add_cancel] using mem

theorem rectangular_semiperiod_nonmembers {t : ℝ} (ht : 0<t) :
    let R := manuscriptRectangularLattice t ht
    (1:ℂ)∉R.lattice ∧ I*t∉R.lattice ∧ 1+I*t∉R.lattice := by
  let R := manuscriptRectangularLattice t ht
  have one : (1:ℂ)∉R.lattice := by simpa [R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair]
    using R.ω₁_div_two_notMem_lattice
  have y : R.ω₂/2=I*t := by dsimp [R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair]; push_cast; ring
  have odd : 1+I*t∉R.lattice := by
    intro h
    obtain ⟨m,n,hr,_⟩ := (slanted_mem_lattice_iff (show 0<2*t by positivity) 0 _).mp h
    simp at hr
    have e : (1:ℤ)=2*m := by exact_mod_cast hr
    omega
  exact ⟨one,y ▸ R.ω₂_div_two_notMem_lattice,odd⟩

/-- Comparison of the actual elliptic functions, including the
constant term fixed by their Laurent expansions at the origin. -/
theorem rhombic_weierstrass_rectangular_trace {t : ℝ} (ht : 0<t) {z : ℂ}
    (off : z∉(rhombicPeriodPair t ht).lattice) :
    let R := manuscriptRectangularLattice t ht
    (rhombicPeriodPair t ht).weierstrassP z=R.weierstrassP z+
      R.weierstrassP (z-(1+I*t))-R.weierstrassP (1+I*t) := by
  let R := manuscriptRectangularLattice t ht
  let L := rhombicPeriodPair t ht
  let p : ℂ := 1+I*t
  let f := fun w => R.weierstrassP w+R.weierstrassP (w-p)
  let g := fun w => R.weierstrassPExcept 0 w+R.weierstrassP (w-p)
  have twice : p+p∈R.lattice := by
    convert R.lattice.add_mem R.ω₁_mem_lattice R.ω₂_mem_lattice using 1
    dsimp [R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair,p]
    push_cast
    ring
  have per₁ : Function.Periodic f L.ω₁ := by
    intro w
    change R.weierstrassP (w+R.ω₁)+R.weierstrassP (w+R.ω₁-p)=_
    rw [show w+R.ω₁-p=w-p+R.ω₁ by ring,R.weierstrassP_add_coe w (⟨_,R.ω₁_mem_lattice⟩ : R.lattice),
      R.weierstrassP_add_coe (w-p) (⟨_,R.ω₁_mem_lattice⟩ : R.lattice)]
  have per₂ : Function.Periodic f L.ω₂ := by
    intro w
    change R.weierstrassP (w+p)+R.weierstrassP (w+p-p)=_
    rw [show w+p=(w-p)+(p+p) by ring,R.weierstrassP_add_coe (w-p) (⟨_,twice⟩ : R.lattice)]
    change _+R.weierstrassP (w-p+(p+p)-p)=R.weierstrassP w+_
    rw [show w-p+(p+p)-p=w by ring,add_comm]
  have per (w v : ℂ) (hv : v∈L.lattice) : f (w+v)=f w := by
    obtain ⟨m,n,rfl⟩ := PeriodPair.mem_lattice.mp hv
    simpa only [zsmul_eq_mul] using! ((per₁.zsmul m).add_period (per₂.zsmul n)) w
  have diff (w : ℂ) (hw : w∉L.lattice) : DifferentiableAt ℂ f w := by
    have both := (rectangular_lattice_and_coset ht w).not.mp hw
    exact (R.analyticOnNhd_weierstrassP _ (fun h => both (Or.inl h))).differentiableAt.add
      ((R.analyticOnNhd_weierstrassP _ (fun h => both (Or.inr h))).differentiableAt.comp w (differentiableAt_id.sub_const p))
  have minus : 0-p∉R.lattice := by
    rw [zero_sub]
    exact fun h => (rectangular_semiperiod_nonmembers ht).2.2 (by simpa only [neg_neg] using R.lattice.neg_mem h)
  have an : AnalyticAt ℂ g 0 := (R.analyticAt_weierstrassPExcept 0).add
    ((R.analyticOnNhd_weierstrassP (0-p) minus).comp (f:=fun w : ℂ => w-p) (analyticAt_id.sub analyticAt_const))
  have principal : ∀ᶠ w in 𝓝 (0:ℂ), w≠0 → f w=1/w^2+g w := by
    filter_upwards with w
    intro _
    have eq : R.weierstrassP w=R.weierstrassPExcept 0 w+1/w^2 := by
      simpa using (R.weierstrassPExcept_add (0:R.lattice) w).symm
    dsimp [f,g]
    rw [eq]
    ring
  have same := elliptic_double_pole_classification L 1 diff per an principal z off
  change f z=1*L.weierstrassP z+g 0 at same
  simp only [f,g,one_mul,R.weierstrassPExcept_zero,zero_sub,R.weierstrassP_neg,zero_add] at same
  change L.weierstrassP z=_
  linear_combination -same

/-- The three half-period values of any lattice are the three distinct
roots of its Weierstrass cubic when the points are distinct modulo the
lattice. The quadratic coefficient of that cubic is zero. -/
theorem marked_three_branch_values_sum (L : PeriodPair) {a b c : ℂ}
    (ha : a∉L.lattice) (hb : b∉L.lattice) (hc : c∉L.lattice)
    (ma : a+a∈L.lattice) (mb : b+b∈L.lattice) (mc : c+c∈L.lattice)
    (ab : b-a∉L.lattice) (ac : c-a∉L.lattice) (bc : c-b∉L.lattice) :
    L.weierstrassP a+L.weierstrassP b+L.weierstrassP c=0 := by
  have crit (x : ℂ) (h : x+x∈L.lattice) : L.derivWeierstrassP x=0 := by
    have same := L.derivWeierstrassP_add_coe (-x) (⟨_,h⟩ : L.lattice)
    rw [show -x+(x+x)=x by ring,L.derivWeierstrassP_neg] at same
    linear_combination same/2
  have different (x y : ℂ) (rx : x∉L.lattice) (ry : y∉L.lattice) (dx : x+x∈L.lattice)
      (dy : y+y∈L.lattice) (h : y-x∉L.lattice) : L.weierstrassP x≠L.weierstrassP y :=
    fun e => h (marked_weierstrass_value_derivative_injective L rx ry e ((crit x dx).trans (crit y dy).symm))
  have root (x : ℂ) (hx : x∉L.lattice) (dx : x+x∈L.lattice) :
      4*L.weierstrassP x^3-L.g₂*L.weierstrassP x-L.g₃=0 := by
    have eq := L.derivWeierstrassP_sq x hx
    rw [crit x dx,zero_pow (by decide : 2≠0)] at eq
    linear_combination -eq
  have pair (x y : ℂ) (hx : x∉L.lattice) (hy : y∉L.lattice) (dx : x+x∈L.lattice)
      (dy : y+y∈L.lattice) (h : y-x∉L.lattice) :
      4*(L.weierstrassP x^2+L.weierstrassP x*L.weierstrassP y+L.weierstrassP y^2)=L.g₂ := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr (different x y hx hy dx dy h))
    linear_combination root x hx dx-root y hy dy
  apply mul_left_cancel₀ (sub_ne_zero.mpr (different b c hb hc mb mc bc))
  linear_combination (pair a b ha hb ma mb ab-pair a c ha hc ma mc ac)/4

theorem rhombic_real_half_value_rectangular {t : ℝ} (ht : 0<t) :
    let R := manuscriptRectangularLattice t ht
    (rhombicPeriodPair t ht).weierstrassP 1= -2*R.weierstrassP (1+I*t) := by
  let R := manuscriptRectangularLattice t ht
  let L := rhombicPeriodPair t ht
  let y : ℂ := I*t
  let p := 1+y
  obtain ⟨one,iy,diagonal⟩ := rectangular_semiperiod_nonmembers ht
  have real2 : (1:ℂ)+1∈R.lattice := by convert R.ω₁_mem_lattice using 1; norm_num [R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair]
  have imag2 : y+y∈R.lattice := by
    convert R.ω₂_mem_lattice using 1
    dsimp [R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair,y]
    push_cast
    ring
  have both : p+p∈R.lattice := by rw [show p+p=(1+1)+(y+y) by dsimp [p];ring]; exact R.lattice.add_mem real2 imag2
  have diff : y-1∉R.lattice := by
    intro h
    apply diagonal
    convert R.lattice.add_mem h real2 using 1
    change 1+y=y-1+(1+1)
    ring
  have values := marked_three_branch_values_sum R one iy diagonal real2 imag2 both diff
    (by simpa [p,y] using iy) (by simpa [p,y] using one)
  have reg : (1:ℂ)∉L.lattice := by convert L.ω₁_div_two_notMem_lattice using 1; norm_num [L,rhombicPeriodPair]
  have trace := rhombic_weierstrass_rectangular_trace ht reg
  change L.weierstrassP 1=R.weierstrassP 1+R.weierstrassP (1-p)-R.weierstrassP p at trace
  rw [show 1-p= -y by dsimp [p];ring,R.weierstrassP_neg] at trace
  change R.weierstrassP 1+R.weierstrassP y+R.weierstrassP p=0 at values
  change L.weierstrassP 1= -2*R.weierstrassP p
  linear_combination trace+values

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_weierstrass_rectangular_trace
#print axioms TwoAxisHelicoid.rhombic_real_half_value_rectangular
