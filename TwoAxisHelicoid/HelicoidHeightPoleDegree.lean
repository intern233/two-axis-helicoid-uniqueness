import TwoAxisHelicoid.HelicoidConnectedUpperEnd
import TwoAxisHelicoid.PowerRightHalfPlaneSheets
import TwoAxisHelicoid.PuncturedEndInverseEscape
import TwoAxisHelicoid.MeromorphicHeightPowerCoordinate

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

private theorem high_height_eventually {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} (cont : Continuous h) {P : M → Prop} (ev : ∀ᶠ x in cocompact M, P x) :
    ∃ B : ℝ, ∀ x, B<h x → P x := by
  obtain ⟨C,cC,sub⟩ := mem_cocompact.mp ev
  obtain ⟨B,bd⟩ := cC.exists_bound_of_continuousOn cont.continuousOn
  exact ⟨B,fun x hx => sub (fun cx => hx.not_ge ((le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs] using bd x cx)))⟩

theorem PuncturedComplexEnd.to_punctured_zero {M : Type*} [TopologicalSpace M] (E : PuncturedComplexEnd M) :
    Tendsto E.coord (cocompact M) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  have src : E.coord.source ∈ cocompact M := by simpa only [compl_compl] using E.compact_core.compl_mem_cocompact
  refine ⟨E.to_zero,?_⟩
  filter_upwards [src] with x hx using E.coord_ne_zero hx

/-- A compactified C¹ helicoidal end cannot have degree greater than
one for a meromorphic complex height. This uses the whole spatial
upper end and the different local sheets of a pole. -/
theorem HasHelicoidC1End.height_pole_degree_one {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (cont : Continuous X)
    (E : PuncturedComplexEnd M) {H : ℂ → ℂ} (mer : MeromorphicAt H 0) {n : ℕ} (hn : 0<n)
    (order : meromorphicOrderAt H 0=((-(n:ℤ):ℤ):WithTop ℤ)) {b : ℝ}
    (height : ∀ᶠ z in 𝓝[≠] (0:ℂ), (X (E.coord.symm z)).2=(H z).re+b) : n=1 := by
  by_contra hne
  have many : 1<n := by omega
  obtain ⟨f,k,af,ak,f0,k0,right,_,normal⟩ := meromorphic_pole_power_coordinate mer hn order
  let P := f ∘ E.coord
  let h := fun x => (X x).2
  have ch : Continuous h := continuous_snd.comp cont
  have src : E.coord.source ∈ cocompact M := by simpa only [compl_compl] using E.compact_core.compl_mem_cocompact
  have ev : ∀ᶠ x in cocompact M, ContinuousAt P x ∧ h x=(((P x)^n)⁻¹).re+b := by
    filter_upwards [src,E.to_zero.eventually af.eventually_continuousAt,E.to_punctured_zero.eventually (height.and normal)]
      with x hx ca v
    refine ⟨ca.comp (E.coord.continuousAt hx),?_⟩
    have eq := v.1
    rw [E.coord.left_inv hx,v.2] at eq
    exact eq
  obtain ⟨D,good⟩ := high_height_eventually ch ev
  obtain ⟨U,conn,lower,B,includes⟩ := (graph.connected_upper_end cont).1 (max D b)
  have inU (x : M) (hx : x∈U) := good x ((le_max_left D b).trans_lt (lower x hx))
  have positive : ∀ z∈P '' U,0<(z^n).re := by
    rintro _ ⟨x,hx,rfl⟩
    have l : b<h x := (le_max_right D b).trans_lt (lower _ hx)
    rw [(inU _ hx).2] at l
    by_contra! neg
    have nn : (((P x)^n)⁻¹).re≤0 := by
      rw [Complex.inv_re]
      exact div_nonpos_of_nonpos_of_nonneg neg (normSq_nonneg _)
    linarith
  have inj := pow_injective_on_connected_right_half_plane hn
    (conn.image P (fun x hx => (inU x hx).1.continuousWithinAt)) positive
  have kt : Tendsto k (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) := by
    simpa only [k0] using ak.continuousAt.continuousWithinAt.tendsto (s := ({0}ᶜ : Set ℂ))
  have kp : Tendsto k (𝓝[≠] (0:ℂ)) (𝓝[≠] (0:ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨kt,?_⟩
    filter_upwards [right.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w eq nz
    exact fun zero => nz (eq.symm.trans ((congrArg f zero).trans f0))
  let x := fun w => E.coord.symm (k w)
  have lift : ∀ᶠ w in 𝓝[≠] (0:ℂ), P (x w)=w ∧ h (x w)=((w^n)⁻¹).re+b := by
    filter_upwards [right.filter_mono nhdsWithin_le_nhds,kp.eventually (height.and normal),
      kt.eventually (ball_mem_nhds (0:ℂ) E.radius_pos),kp.eventually self_mem_nhdsWithin] with w inv eq small nz
    have mem := E.mem_target_of_ball_ne small nz
    refine ⟨(congrArg f (E.coord.right_inv mem)).trans inv,?_⟩
    exact eq.1.trans (by rw [eq.2,inv])
  obtain ⟨δ,hδ,near⟩ := Metric.mem_nhdsWithin_iff.mp lift
  obtain ⟨z,w,ne,zp,zd,wp,wd,pow,high⟩ := distinct_small_equal_positive_power many hδ (B-b)
  have get (v : ℂ) (pos : 0<‖v‖) (small : ‖v‖<δ) (large : B-b<((v^n)⁻¹).re) : v∈P '' U := by
    have d := near (show v∈ball (0:ℂ) δ ∩ {0}ᶜ from ⟨by rwa [mem_ball,dist_zero_right],norm_pos_iff.mp pos⟩)
    refine ⟨x v,includes _ ?_,d.1⟩
    change B<h (x v)
    rw [d.2]
    linarith
  exact ne (inj (get z zp zd high) (get w wp wd (pow ▸ high)) pow)

/-- Meromorphicity of a complex height primitive alone forces its
simple pole and the double pole of the height differential. No
singularity order, residue or leading term is assumed. -/
theorem HasHelicoidC1End.meromorphic_height_orders {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (cont : Continuous X)
    (E : PuncturedComplexEnd M) {H : ℂ → ℂ} (mer : MeromorphicAt H 0) {b : ℝ}
    (height : ∀ᶠ z in 𝓝[≠] (0:ℂ), (X (E.coord.symm z)).2=(H z).re+b) :
    meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ) ∧ MeromorphicAt (deriv H) 0 ∧
      meromorphicOrderAt (deriv H) 0=((-2:ℤ):WithTop ℤ) := by
  have negative : meromorphicOrderAt H 0<0 := by
    by_contra! ge
    obtain ⟨v,limit⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg mer).mpr ge
    have bound : ∀ᶠ z in 𝓝[≠] (0:ℂ), (X (E.coord.symm z)).2<v.re+b+1 := by
      have l : Tendsto (fun z => (H z).re+b) (𝓝[≠] (0:ℂ)) (𝓝 (v.re+b)) :=
        (continuous_re.continuousAt.tendsto.comp limit).add_const b
      filter_upwards [height,l.eventually (gt_mem_nhds (lt_add_one (v.re+b)))] with z eq h using eq.trans_lt h
    have src : E.coord.source∈cocompact M := by simpa only [compl_compl] using E.compact_core.compl_mem_cocompact
    have ev : ∀ᶠ x in cocompact M, (X x).2<v.re+b+1 := by
      filter_upwards [src,E.to_punctured_zero.eventually bound] with x hx h
      rwa [E.coord.left_inv hx] at h
    obtain ⟨D,hD⟩ := high_height_eventually (continuous_snd.comp cont) ev
    obtain ⟨x,hx⟩ := ((graph.connected_upper_end cont).2 (max D (v.re+b+1))).1
    exact ((le_max_right D (v.re+b+1)).trans_lt hx).not_ge (hD x ((le_max_left _ _).trans_lt hx)).le
  obtain ⟨m,hm⟩ := WithTop.ne_top_iff_exists.mp negative.ne_top
  have mn : m<0 := by
    apply WithTop.coe_lt_coe.mp
    rw [hm,WithTop.coe_zero]
    exact negative
  have simple : meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ) := by
    cases m with
    | ofNat j => exact ((Int.natCast_nonneg j).not_gt mn).elim
    | negSucc j =>
      have order : meromorphicOrderAt H 0=((-(j.succ:ℤ):ℤ):WithTop ℤ) := hm.symm
      have one := graph.height_pole_degree_one cont E mer (n := j.succ) (Nat.succ_pos j) order height
      have eq : j=0 := Nat.succ.inj one
      subst j
      exact hm.symm
  exact ⟨simple,mer.deriv,meromorphicOrderAt_deriv_eq_sub_one (𝕜 := ℂ) (n := (-1:ℤ)) (by norm_num) simple⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.height_pole_degree_one
#print axioms TwoAxisHelicoid.HasHelicoidC1End.meromorphic_height_orders
