import TwoAxisHelicoid.CertifiedCompactDoublePoints
import TwoAxisHelicoid.GaussLevelTangent
import TwoAxisHelicoid.WeierstrassCoordinateData
import TwoAxisHelicoid.WeierstrassFibers

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff ComplexConjugate
set_option maxHeartbeats 1200000

/-- Failure of global embeddedness of the certified explicit model
produces an actual double point of maximal spatial height. At one
of its two preimages the height differential vanishes, or the two
Gauss phases agree modulo π. -/
theorem certified_nonembedded_height_extremal_pair (fails : ¬ IsClosedEmbedding certifiedTorusImmersion) :
    let p := certifiedClosedParameters
    let L := certifiedPeriodPair
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let G := thetaGauss p.t p.a 1
    ∃ z w : ℂ, z∉L.lattice ∧ w∉L.lattice ∧ periodTorusProjection L z≠periodTorusProjection L w ∧
      X z=X w ∧ (∀ u v, u∉L.lattice → v∉L.lattice → periodTorusProjection L u≠periodTorusProjection L v →
        X u=X v → X u 2≤X z 2) ∧
      (z-p.a∈L.lattice ∨ z+p.a∈L.lattice ∨ w-p.a∈L.lattice ∨ w+p.a∈L.lattice ∨ (conj (G z)*G w).im=0) := by
  let p := certifiedClosedParameters
  let L := certifiedPeriodPair
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let F := certifiedTorusImmersion
  let height := fun q : PuncturedPeriodTorus L × PuncturedPeriodTorus L => F q.1 2
  obtain ⟨compact,K,_,_,criterion⟩ := certified_compact_embedding_criterion
  have nonempty : (immersionDoublePoints F).Nonempty := by
    by_contra h
    apply fails
    apply criterion.mpr
    intro x _ y _ eq
    by_contra ne
    exact h ⟨(x,y),eq,ne⟩
  have cont : Continuous height :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 2).comp (certifiedTorusImmersion_continuous.comp continuous_fst)
  obtain ⟨⟨q,r⟩,pair,maximum⟩ := compact.exists_isMaxOn nonempty cont.continuousOn
  obtain ⟨z,ez⟩ := Quotient.exists_rep q.1
  obtain ⟨w,ew⟩ := Quotient.exists_rep r.1
  change periodTorusProjection L z=q.1 at ez
  change periodTorusProjection L w=r.1 at ew
  have hz : z∉L.lattice := fun h => q.2 (ez.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
  have hw : w∉L.lattice := fun h => r.2 (ew.symm.trans ((periodTorusProjection_eq_zero L w).mpr h))
  let π := fun (u : ℂ) (hu : u∉L.lattice) => (⟨periodTorusProjection L u,fun e => hu ((periodTorusProjection_eq_zero L u).mp e)⟩ : PuncturedPeriodTorus L)
  have image (u : ℂ) (hu : u∉L.lattice) : F (π u hu)=coordinateToEuclidean (X u) := rfl
  have Q : π z hz=q := Subtype.ext ez
  have R : π w hw=r := Subtype.ext ew
  have different : periodTorusProjection L z≠periodTorusProjection L w :=
    fun h => pair.2 (Subtype.ext (ez.symm.trans (h.trans ew)))
  have same : X z=X w := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective
    have identified : F (π z hz)=F (π w hw) := by rw [Q,R]; exact pair.1
    exact (image z hz).symm.trans (identified.trans (image w hw))
  have upper (u v : ℂ) (hu : u∉L.lattice) (hv : v∉L.lattice)
      (ne : periodTorusProjection L u≠periodTorusProjection L v) (eq : X u=X v) : X u 2≤X z 2 := by
    have sat : (π u hu,π v hv)∈immersionDoublePoints F :=
      ⟨(image u hu).trans ((congrArg coordinateToEuclidean eq).trans (image v hv).symm),
        fun e => ne (congrArg Subtype.val e)⟩
    have e := maximum sat
    change F (π u hu) 2≤F q 2 at e
    rwa [← Q,image,image] at e
  refine ⟨z,w,hz,hw,different,same,upper,?_⟩
  by_cases zm : z-p.a∈L.lattice
  · exact Or.inl zm
  by_cases zp : z+p.a∈L.lattice
  · exact Or.inr (Or.inl zp)
  by_cases wm : w-p.a∈L.lattice
  · exact Or.inr (Or.inr (Or.inl wm))
  by_cases wp : w+p.a∈L.lattice
  · exact Or.inr (Or.inr (Or.inr (Or.inl wp)))
  apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
  let C := coordinateData p.t p.a 1 p.height_pos
  let G := thetaGauss p.t p.a 1
  have heightReg (u : ℂ) (hu : u∉L.lattice) (hm : u-p.a∉L.lattice) (hp : u+p.a∉L.lattice) : C u 2≠0 := by
    have pa := real_not_mem_rhombic_lattice_of_pos p.height_pos p.abscissa_mem.1 (by linarith [p.abscissa_mem.2] : p.a<2)
    have reg : L.weierstrassP u≠L.weierstrassP p.a := fun e => (rhombic_weierstrassP_eq_iff p.height_pos pa hu).mp e |>.elim hm hp
    change I*(1:ℂ)*(L.weierstrassP u-L.weierstrassP p.a)≠0
    exact mul_ne_zero (mul_ne_zero I_ne_zero one_ne_zero) (sub_ne_zero.mpr reg)
  have hnz := heightReg z hz zm zp
  have hnw := heightReg w hw wm wp
  have za : C z=weierstrassTriple (G z) (C z 2) := coordinateData_eq_original p.height_pos p.abscissa_mem hz zm zp
  have wa : C w=weierstrassTriple (G w) (C w 2) := coordinateData_eq_original p.height_pos p.abscissa_mem hw wm wp
  have model := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  have cp : Continuous (periodTorusProjection L) := QuotientAddGroup.continuous_mk
  have localBound : ∀ᶠ t : ℂ × ℂ in 𝓝 (z,w), X t.1=X t.2 → X t.1 2≤X z 2 := by
    have left : ContinuousAt (fun t : ℂ × ℂ => periodTorusProjection L t.1) (z,w) := (cp.comp continuous_fst).continuousAt
    have right : ContinuousAt (fun t : ℂ × ℂ => periodTorusProjection L t.2) (z,w) := (cp.comp continuous_snd).continuousAt
    filter_upwards [continuous_fst.continuousAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz),
      continuous_snd.continuousAt (L.isClosed_lattice.isOpen_compl.mem_nhds hw),
      (left.ne_iff_eventually_ne right).mp different] with t ht hs ne using upper t.1 t.2 ht hs ne
  have singular := height_maximal_double_point_not_surjective X X (model.2.1 z hz).contDiffAt (model.2.1 w hw).contDiffAt same localBound
  rw [(model.2.2.2 z hz).1.fderiv,(model.2.2.2 w hw).1.fderiv] at singular
  apply (levelTangent_det_zero_iff hnz hnw).mp
  change levelTangent (weierstrassTriple (G z) (C z 2)) 0*_ - _*_=0
  rw [← za,← wa]
  by_contra det
  exact singular (double_point_height_surjective_of_level_det hnz hnw det)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_nonembedded_height_extremal_pair
