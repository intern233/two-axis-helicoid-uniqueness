import TwoAxisHelicoid.CentralBandEdgeData
import TwoAxisHelicoid.CertifiedFirstSpatialDisk
import TwoAxisHelicoid.OriginalSlopingPeriod

namespace TwoAxisHelicoid
open Complex Set ComplexBall
attribute [local irreducible] thetaA thetaJet thetaGauss

private theorem certified_band_height_input :
    (TraceData.slopingFluxParams.height.interpret.toBall slopingFluxAnalyticSetup.config.prec).Contains (certifiedClosedParameters.t:ℂ) :=
  coarsen_contains (realInterval_contains certifiedClosedParameters_bounds.1.1.le certifiedClosedParameters_bounds.1.2.le) firstDiskNumbers.2.2.2

theorem CentralGaussFieldTrace.sound (w : CentralGaussFieldTrace) (v : w.Valid) {z : ℂ}
    (inside : (w.box.toBall slopingFluxAnalyticSetup.config.prec).Contains z)
    (strip : z.im∈Ioo 0 certifiedClosedParameters.t) :
    (w.result.output.toBall slopingFluxAnalyticSetup.config.prec).Contains
      (thetaGauss certifiedClosedParameters.t certifiedClosedParameters.a 1 z) := by
  let p := certifiedClosedParameters
  let S := slopingFluxAnalyticSetup
  obtain ⟨base,second,hh,lb,out⟩ := v
  obtain ⟨ht,ha⟩ := certifiedClosedParameters_bounds
  obtain ⟨lo,q,a,c,_⟩ := sloping_flux_root_parameter_enclosures (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self ha)
  have tail := S.tail_bound_one slopingFluxAnalyticSetup_valid lo
  have val := w.base.sound S.config S.terms S.error q a c inside (tail 0) (tail 1) base
  obtain ⟨arg,_,yi,_,seed,_,d0,d1,_⟩ := base
  have av := w.base.argument.sound S.config _ _ (threeDyadic_contains inside a (DyadicBall.zero_contains _)) _ arg
  rw [value_thetaArgumentExpression] at av
  have se := w.base.seed.sound S.config av seed
  have im := DyadicBall.im_le_one av yi
  have h0 := w.base.theta0.sound S.config 0 S.terms S.error q _ se (tail 0 _ im) d0
  have h1 := w.base.theta1.sound S.config 1 S.terms S.error q _ se (tail 1 _ im) d1
  have rem2 := firstDiskTail.remainder_bound S.config (4/5) 1 2 5 1048576 (DyadicThetaTail.valid_of_checks firstDiskTail_valid)
    (by norm_num) lo (by simpa only [Rat.cast_one] using im)
  have h2 := w.second.sound S.config 2 S.terms S.error q _ se rem2 second
  have hH := w.height.sound S.config _ _ (fiveDyadic_contains certified_band_height_input h0 h1 h2 (DyadicBall.zero_contains _)) _ hh
  let t := p.t
  have al : spatialHeightExpression.value (fiveValues t (thetaJet t 0 (Real.pi*z/2)) (thetaJet t 1 (Real.pi*z/2))
      (thetaJet t 2 (Real.pi*z/2)) 0)=I*(thetaLogSecond t z-(Real.pi/t:ℝ)) := by
    simp [spatialHeightExpression,BallExpression.value,BallExpression.value_pow,BallExpression.value_div,BallExpression.value_sub,
      BallExpression.value_imaginaryUnit,thetaLogSecond,thetaQuotient,fiveValues]
    ring_nf
    exact Or.inl True.intro
  rw [al] at hH
  let L := rhombicPeriodPair t p.height_pos
  have off := rhombic_horizontal_strip_not_mem p.height_pos strip
  have offa := real_not_mem_rhombic_lattice_of_pos p.height_pos p.abscissa_mem.1 (show p.a<2 by linarith [p.abscissa_mem.2])
  have hP := thetaLogSecond_eq_weierstrassP_add_eta_of_pos p.height_pos p.height_pos off
  have hA := thetaG_eq_weierstrassP_of_pos p.height_pos p.height_pos p.a offa
  rw [p.vertical_closed] at hA
  have diff : thetaLogSecond t z-(Real.pi/t:ℝ)=L.weierstrassP z-L.weierstrassP p.a := by linear_combination hP-hA
  rw [diff] at hH
  have nz := ComplexBall.ne_zero_of_lower_pos hH (DyadicBall.lower_pos_toBall lb)
  have value := w.result.sound S.config _ _ (threeDyadic_contains val.1 hH (DyadicBall.zero_contains _)) _ out
  change (w.result.output.toBall S.config.prec).Contains ((BallExpression.div (.input 0) (.input 1)).value _) at value
  simp only [BallExpression.value_div,BallExpression.value,threeValues] at value
  have plus : z+p.a∉L.lattice := rhombic_horizontal_strip_not_mem p.height_pos (by
    change (z+(p.a:ℂ)).im∈Ioo 0 t
    simpa only [add_im,ofReal_im,add_zero] using strip)
  have prod := thetaGauss_height_sigma_of_pos p.height_pos p.height_pos 1 offa off plus
  rw [thetaSigmaKernel_eq_thetaA_of_pos p.height_pos p.height_pos z offa off] at prod
  simp only [ofReal_one,mul_one,one_mul] at prod
  exact (eq_div_iff nz).mpr prod ▸ value

noncomputable def centralBandEdgePoint (v : Bool) (c s : ℝ) : ℂ := if v then ⟨c,s⟩ else ⟨s,c⟩

private theorem centralBandEdgeBall_contains {v : Bool} {c l r : ℚ} {s : ℝ} (hs : s∈Icc (l:ℝ) r) :
    (centralBandEdgeBall v c l r).Contains (centralBandEdgePoint v c s) := by
  have bound : |s-((l+r)/2:ℚ)|≤((r-l)/2:ℚ) := by
    push_cast
    exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  cases v
  · change ‖(⟨s,(c:ℝ)⟩:ℂ)-(⟨(((l+r)/2:ℚ):ℝ),(c:ℝ)⟩:ℂ)‖≤((r-l)/2:ℚ)
    rwa [show (⟨s,(c:ℝ)⟩:ℂ)-(⟨(((l+r)/2:ℚ):ℝ),(c:ℝ)⟩:ℂ)=((s-((l+r)/2:ℚ):ℝ):ℂ) by apply Complex.ext <;> simp,Complex.norm_real,Real.norm_eq_abs]
  · change ‖(⟨(c:ℝ),s⟩:ℂ)-(⟨(c:ℝ),(((l+r)/2:ℚ):ℝ)⟩:ℂ)‖≤((r-l)/2:ℚ)
    rwa [show (⟨(c:ℝ),s⟩:ℂ)-(⟨(c:ℝ),(((l+r)/2:ℚ):ℝ)⟩:ℂ)=I*((s-((l+r)/2:ℚ):ℝ):ℂ) by apply Complex.ext <;> simp,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]

noncomputable def CentralBandQuantity.holds (k : CentralBandQuantity) (z : ℂ) : Prop :=
  let p := certifiedClosedParameters
  let H := actualComplexHeight p.t p.a 1 p.height_pos
  let g := thetaGauss p.t p.a 1
  match k with
  | .heightNeg => (H z).re<0
  | .heightPos => 0<(H z).re
  | .gauss => (g z).re≤ -(1/512) ∧ (g z).im≤ -(1/512)

theorem CheckedCentralBandEdge.sound {k v c l r} (checked : CheckedCentralBandEdge k v c l r) :
    ∀ s∈Icc (l:ℝ) r, (centralBandEdgePoint v c s).im∈Ioo 0 certifiedClosedParameters.t →
      k.holds (centralBandEdgePoint v c s) := by
  let p := certifiedClosedParameters
  let S := slopingFluxAnalyticSetup
  obtain ⟨ht,ha⟩ := certifiedClosedParameters_bounds
  obtain ⟨lo,q,_,_,_⟩ := sloping_flux_root_parameter_enclosures (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self ha)
  induction checked with
  | heightNeg w ok =>
    obtain ⟨val,box,neg⟩ := ok
    intro s hs _
    have e := w.sound S slopingFluxAnalyticSetup_valid val p.height_pos p.abscissa_mem p.vertical_closed lo
      certified_band_height_input q (coarsen_contains (centralBandEdgeBall_contains hs) box)
    exact (re_bounds e.2).2.trans_lt (by exact_mod_cast neg)
  | heightPos w ok =>
    obtain ⟨val,box,pos⟩ := ok
    intro s hs _
    have e := w.sound S slopingFluxAnalyticSetup_valid val p.height_pos p.abscissa_mem p.vertical_closed lo
      certified_band_height_input q (coarsen_contains (centralBandEdgeBall_contains hs) box)
    exact lt_of_lt_of_le (by exact_mod_cast pos) (re_bounds e.2).1
  | @gauss w v c l r ok =>
    obtain ⟨val,box,real,imag⟩ := ok
    intro s hs hy
    have e := w.sound val (coarsen_contains (centralBandEdgeBall_contains hs) box) hy
    let B := w.result.output.toBall S.config.prec
    let g := thetaGauss p.t p.a 1 (centralBandEdgePoint v c s)
    have u := (Complex.abs_im_le_norm (g-B.center.val)).trans e
    change |g.im-(B.center.im:ℝ)|≤(B.radius:ℝ) at u
    have br : ((B.center.re+B.radius:ℚ):ℝ)≤((-(1/512:ℚ)):ℝ) := by exact_mod_cast real
    have bi : ((B.center.im+B.radius:ℚ):ℝ)≤((-(1/512:ℚ)):ℝ) := by exact_mod_cast imag
    refine ⟨(re_bounds e).2.trans (by simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using br),?_⟩
    change g.im≤ -(1/512:ℝ)
    push_cast at bi
    linarith [(abs_le.mp u).2]
  | @join k v c l m r _ _ a b =>
    intro s hs h
    rcases le_total s (m:ℝ) with lower|upper
    · exact a s ⟨hs.1,lower⟩ h
    · exact b s ⟨upper,hs.2⟩ h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedCentralBandEdge.sound
