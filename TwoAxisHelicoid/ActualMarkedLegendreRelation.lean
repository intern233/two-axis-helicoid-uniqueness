import TwoAxisHelicoid.MarkedParallelogramResidue
import TwoAxisHelicoid.MarkedWeierstrassZeta

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter Topology

theorem marked_cell_generator_paths (L : PeriodPair) (s : ℝ) :
    markedCellBase L+(s:ℂ)*L.ω₁∉L.lattice ∧ markedCellBase L+(s:ℂ)*L.ω₂∉L.lattice := by
  have horizontal := puncture_square_side_regular L (-1/2) (-1/2) (1/2) (-1/2) s 1 zero_lt_one le_rfl (Or.inr ⟨rfl,Or.inl rfl⟩)
  have vertical := puncture_square_side_regular L (-1/2) (-1/2) (-1/2) (1/2) s 1 zero_lt_one le_rfl (Or.inl ⟨rfl,Or.inl rfl⟩)
  constructor
  · convert horizontal using 2
    simp [markedCellBase,spinSquareLinear,Complex.real_smul]
    ring
  · convert vertical using 2
    simp [markedCellBase,spinSquareLinear,Complex.real_smul]
    ring

private theorem marked_regular_part_boundary (L : PeriodPair) :
    punctureBoundaryIntegral L (fun z => z*L.weierstrassPExcept 0 z) 1=0 := by
  let J := fun z => z*L.weierstrassPExcept 0 z
  have ok (z : ℂ) (hz : z∉L.lattice ∨ z=0) : DifferentiableAt ℂ J z := by
    have inside : z∈((L.lattice:Set ℂ) \ {0})ᶜ := by
      intro h
      exact hz.elim (fun off => off h.1) (fun eq => h.2 eq)
    exact differentiableAt_id.mul (L.differentiableOn_weierstrassPExcept 0 |>.differentiableAt
      (L.isOpen_compl_lattice_sdiff.mem_nhds inside))
  have side (x y u v : ℝ) (boundary : (x=u ∧ (x= -1/2 ∨ x=1/2)) ∨ (y=v ∧ (y= -1/2 ∨ y=1/2))) :=
    dilated_edge_stokes (f:=J) (spinSquareLinear L x y) (spinSquareLinear L u v) zero_le_one (fun t ht s _ => by
      apply ok
      by_cases h : t=0
      · right; simp [h]
      · exact Or.inl (puncture_square_side_regular L x y u v s t (lt_of_le_of_ne ht.1 (Ne.symm h)) ht.2 boundary))
  have bottom := side (-1/2) (-1/2) (1/2) (-1/2) (Or.inr ⟨rfl,Or.inl rfl⟩)
  have top := side (-1/2) (1/2) (1/2) (1/2) (Or.inr ⟨rfl,Or.inr rfl⟩)
  have left := side (-1/2) (-1/2) (-1/2) (1/2) (Or.inl ⟨rfl,Or.inl rfl⟩)
  have right := side (1/2) (-1/2) (1/2) (1/2) (Or.inl ⟨rfl,Or.inr rfl⟩)
  have zero (a b : ℂ) : dilatedEdgeIntegral J a b 0=0 := by simp [dilatedEdgeIntegral]
  simp only [zero,sub_zero] at bottom top left right
  change punctureBoundaryIntegral L J 1=0
  unfold punctureBoundaryIntegral
  linear_combination bottom+right-top-left

/-- Multiplying the actual elliptic function by z expresses the
two generator periods as one oriented contour integral. -/
theorem marked_weighted_period_difference (L : PeriodPair) :
    let a := markedCellBase L
    punctureBoundaryIntegral L (fun z => z*L.weierstrassP z) 1 =
      L.ω₁*ellipticLinePeriod L.weierstrassP a L.ω₂-
        L.ω₂*ellipticLinePeriod L.weierstrassP a L.ω₁ := by
  let a := markedCellBase L
  let W := fun z => z*L.weierstrassP z
  have shift (d v : ℂ) (hv : v∈L.lattice) (reg : ∀ s∈Icc (0:ℝ) 1, a+(s:ℂ)*d∉L.lattice) :
      ellipticLinePeriod W (a+v) d=ellipticLinePeriod W a d+v*ellipticLinePeriod L.weierstrassP a d := by
    have iW := ellipticLinePeriod_integrable L (f:=W) (fun z hz => differentiableAt_id.mul (L.analyticOnNhd_weierstrassP z hz).differentiableAt) reg
    have iP := ellipticLinePeriod_integrable L (fun z hz => (L.analyticOnNhd_weierstrassP z hz).differentiableAt) reg
    unfold ellipticLinePeriod
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add iW (iP.const_mul v)]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp [W]
    rw [show a+v+(s:ℂ)*d=a+(s:ℂ)*d+v by ring,L.weierstrassP_add_coe _ (⟨v,hv⟩ : L.lattice)]
    ring
  rw [marked_cell_boundary]
  change ellipticLinePeriod W a L.ω₁+ellipticLinePeriod W (a+L.ω₁) L.ω₂-
    ellipticLinePeriod W (a+L.ω₂) L.ω₁-ellipticLinePeriod W a L.ω₂=_
  rw [shift L.ω₂ L.ω₁ L.ω₁_mem_lattice (fun s _ => (marked_cell_generator_paths L s).2),
    shift L.ω₁ L.ω₂ L.ω₂_mem_lattice (fun s _ => (marked_cell_generator_paths L s).1)]
  ring

private theorem marked_weighted_residue (τ : ℂ) (upper : 0<τ.im) :
    let L := upperMarkedLattice τ upper
    punctureBoundaryIntegral L (fun z => z*L.weierstrassP z) 1=2*(Real.pi:ℂ)*I := by
  let L := upperMarkedLattice τ upper
  let a := markedCellBase L
  let J := fun z => z*L.weierstrassPExcept 0 z
  let W := fun z => z*L.weierstrassP z
  let invz := fun z : ℂ => z⁻¹
  have split (b d : ℂ) (reg : ∀ s∈Icc (0:ℝ) 1, b+(s:ℂ)*d∉L.lattice) :
      ellipticLinePeriod W b d=ellipticLinePeriod invz b d+ellipticLinePeriod J b d := by
    have iZ := ellipticLinePeriod_integrable L (f:=invz) (fun z hz => differentiableAt_id.inv (fun eq => hz (eq ▸ L.lattice.zero_mem))) reg
    have iJ := ellipticLinePeriod_integrable L (f:=J) (fun z hz => differentiableAt_id.mul
      (L.differentiableOn_weierstrassPExcept 0 |>.differentiableAt
        (L.isOpen_compl_lattice_sdiff.mem_nhds (fun h => hz h.1)))) reg
    unfold ellipticLinePeriod
    rw [← intervalIntegral.integral_add iZ iJ]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    let z := b+(s:ℂ)*d
    have nz : z≠0 := by
      intro e
      apply reg s hs
      change z∈L.lattice
      rw [e]
      exact L.lattice.zero_mem
    have wp : L.weierstrassP z=L.weierstrassPExcept 0 z+1/z^2 := by
      simpa using (L.weierstrassPExcept_add (0:L.lattice) z).symm
    change d*(z*L.weierstrassP z)=d*z⁻¹+d*(z*L.weierstrassPExcept 0 z)
    rw [wp]
    field_simp [nz]
    ring
  have translated {b v : ℂ} (off : b∉L.lattice) (mem : v∈L.lattice) : b+v∉L.lattice :=
    fun h => off (by simpa only [add_sub_cancel_right] using L.lattice.sub_mem h mem)
  have right (s : ℝ) : a+L.ω₁+(s:ℂ)*L.ω₂∉L.lattice := by
    rw [add_right_comm]
    exact translated (marked_cell_generator_paths L s).2 L.ω₁_mem_lattice
  have top (s : ℝ) : a+L.ω₂+(s:ℂ)*L.ω₁∉L.lattice := by
    rw [add_right_comm]
    exact translated (marked_cell_generator_paths L s).1 L.ω₂_mem_lattice
  have sum : punctureBoundaryIntegral L W 1=punctureBoundaryIntegral L invz 1+punctureBoundaryIntegral L J 1 := by
    simp only [marked_cell_boundary]
    change ellipticLinePeriod W a L.ω₁+ellipticLinePeriod W (a+L.ω₁) L.ω₂-
      ellipticLinePeriod W (a+L.ω₂) L.ω₁-ellipticLinePeriod W a L.ω₂=_
    rw [split a L.ω₁ (fun s _ => (marked_cell_generator_paths L s).1),split (a+L.ω₁) L.ω₂ (fun s _ => right s),
      split (a+L.ω₂) L.ω₁ (fun s _ => top s),split a L.ω₂ (fun s _ => (marked_cell_generator_paths L s).2)]
    dsimp only [a]
    abel
  change punctureBoundaryIntegral L W 1=_
  rw [sum,show punctureBoundaryIntegral L J 1=0 from marked_regular_part_boundary L,add_zero]
  exact upper_marked_inverse_residue τ upper

/-- Genuine period integral of the elliptic coefficient on any
straight marked generator avoiding the pole lattice. -/
theorem marked_weierstrass_period (L : PeriodPair) {b d : ℂ} (hd : d∈L.lattice)
    (avoid : ∀ s∈Icc (0:ℝ) 1, b+(s:ℂ)*d∉L.lattice) :
    ellipticLinePeriod L.weierstrassP b d= -markedZetaIncrement L d := by
  have off : b∉L.lattice := by simpa using avoid 0 (by norm_num)
  rw [marked_line_primitive (F:=fun w => -markedWeierstrassZeta L w)
    (fun s hs => by
      have h := (marked_zeta_hasDerivAt L (avoid s hs)).neg
      change HasDerivAt (fun w => -markedWeierstrassZeta L w) (-(-L.weierstrassP _)) _ at h
      exact h.congr_deriv (neg_neg _))
    (fun s hs => (L.analyticOnNhd_weierstrassP _ (avoid s hs)).continuousAt)]
  linear_combination -(marked_zeta_full_period L off hd)

/-- Legendre's relation with the full, actual zeta increments, in any
marking Γ = ⟨1,τ⟩ with Im τ > 0. -/
theorem marked_full_quasiperiod_legendre (τ : ℂ) (upper : 0<τ.im) :
    let L := upperMarkedLattice τ upper
    markedZetaIncrement L 1*τ-markedZetaIncrement L τ=2*(Real.pi:ℂ)*I := by
  let L := upperMarkedLattice τ upper
  have periods := marked_weighted_period_difference L
  dsimp only at periods
  rw [marked_weierstrass_period L L.ω₁_mem_lattice (fun s _ => (marked_cell_generator_paths L s).1),
    marked_weierstrass_period L L.ω₂_mem_lattice (fun s _ => (marked_cell_generator_paths L s).2)] at periods
  have residue := marked_weighted_residue τ upper
  change punctureBoundaryIntegral L _ 1=2*(Real.pi:ℂ)*I at residue
  change punctureBoundaryIntegral L _ 1=1*(-markedZetaIncrement L τ)-τ*(-markedZetaIncrement L 1) at periods
  change markedZetaIncrement L 1*τ-markedZetaIncrement L τ=_
  linear_combination residue-periods

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_weighted_period_difference
#print axioms TwoAxisHelicoid.marked_weierstrass_period
#print axioms TwoAxisHelicoid.marked_full_quasiperiod_legendre
