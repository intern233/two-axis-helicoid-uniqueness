import TwoAxisHelicoid.RhombicCellHeightSigns
import TwoAxisHelicoid.RhombicCellPhaseExtrema
import TwoAxisHelicoid.RhombicClosedCellPhase
import TwoAxisHelicoid.HelicoidPhaseLevel
import TwoAxisHelicoid.RectanglePhaseExtrema

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology

private theorem cell_relative_phase_im {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X) (hi : Function.Injective (harmonicTorusImmersion hX))
    (α b : ℝ) {z : ℂ} (inS : z∈regularClosedRhombicAxisCell t)
    (xlo : -1<z.re) (xhi : z.re<0) {θ : ℝ}
    (form : exp ((θ:ℂ)*I)=rhombicStripDirection (-1) (fun w => helicoidRelativeHorizontal α b (X w)) z) :
    Real.sin θ=0 ↔ (helicoidRelativeHorizontal α b (X z)).im=0 := by
  let P := fun w => helicoidRelativeHorizontal α b (X w)
  have reg := ((regularClosedRhombicAxisCell_iff ht _).mp inS).2
  have nz : P z≠0 := by
    intro eq
    obtain ⟨k,ek⟩ := (rhombic_physical_axes_preimages ht hX hi reg).1.mp ((helicoidRelativeHorizontal_eq_zero_iff α b _).mp eq)
    have kl : (-1:ℤ)<k := by exact_mod_cast (ek ▸ xlo)
    have kr : k<(0:ℤ) := by exact_mod_cast (ek ▸ xhi)
    omega
  have e : exp ((θ:ℂ)*I)=NormedSpace.normalize (P z) := by
    simpa [rhombicStripDirection,xlo.ne',xhi.ne,P] using form
  have ee := congrArg im e
  change (exp ((θ:ℂ)*I)).im=(NormedSpace.normalize (P z)).im at ee
  rw [exp_ofReal_mul_I_im] at ee
  rw [ee]
  change (NormedSpace.normalize (P z)).im=0 ↔ (P z).im=0
  simp only [NormedSpace.normalize,Complex.real_smul,Complex.im_ofReal_mul,mul_eq_zero,inv_eq_zero,norm_eq_zero,or_iff_right nz]

/-- The closed lift and the horizontal-axis preimage identify the two
boundary phase constants. Their only possible values are integer
multiples of π, also at the corners at infinity. -/
theorem closed_cell_horizontal_phase_constants {t α b : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X) (hi : Function.Injective (harmonicTorusImmersion hX))
    (align : range (axisRuledHelicoid I α b)=range (axisRuledHelicoid I α 0))
    {F : unitInterval × unitInterval → ℝ} (cF : Continuous F)
    (rep : ∀ p, rhombicCellPoint t p∈regularClosedRhombicAxisCell t → exp ((F p:ℂ)*I)=
      rhombicStripDirection (-1) (fun w => helicoidRelativeHorizontal α b (X w)) (rhombicCellPoint t p)) :
    ∃ n m : ℤ, (∀ x, F (x,0)=n*Real.pi) ∧ ∀ x, F (x,1)=m*Real.pi := by
  have edge (y : unitInterval) (edgeY : y=0 ∨ y=1) : ∃ n : ℤ, ∀ x, F (x,y)=n*Real.pi := by
    let g := fun x : unitInterval => F (x,y)
    have cg : Continuous g := cF.comp (continuous_id.prodMk continuous_const)
    have interior : EqOn (fun x => Real.sin (g x)) (fun _ => 0) (Ioo (0:unitInterval) 1) := by
      intro x hx
      let z := rhombicCellPoint t (x,y)
      have xb : -1<z.re ∧ z.re<0 := ⟨by change -1<(x:ℝ)-1; linarith [show (0:ℝ)<x from hx.1],
        by change (x:ℝ)-1<0; linarith [show (x:ℝ)<1 from hx.2]⟩
      have inS := rhombicCellPoint_mem ht (x,y)
      have reg : z∉(rhombicPeriodPair t ht).lattice := by
        intro lat
        rcases (closedRhombicAxisCell_lattice_points ht inS).mp lat with e | e
        · exact xb.2.ne (congrArg re e)
        · exact xb.1.ne' (congrArg re e)
      have good := (regularClosedRhombicAxisCell_iff ht _).mpr ⟨inS,reg⟩
      have hz : ∃ k : ℤ, z.im=k*t := by
        rcases edgeY with rfl | rfl
        · exact ⟨0,by simp [z,rhombicCellPoint]⟩
        · exact ⟨1,by simp [z,rhombicCellPoint]⟩
      have xy := (rhombic_physical_axes_preimages ht hX hi reg).2.mpr hz
      exact (cell_relative_phase_im ht hX hi α b good xb.1 xb.2 (rep _ good)).mpr
        ((aligned_relative_horizontal_at_height_zero align _ xy.2).mpr xy.1)
    have full := interior.closure (Real.continuous_sin.comp cg) continuous_const
    rw [closure_Ioo (zero_ne_one : (0:unitInterval)≠1)] at full
    exact continuous_phase_sin_zero_constant 0 cg (fun x => full ⟨bot_le,le_top⟩)
  obtain ⟨n,hn⟩ := edge 0 (Or.inl rfl)
  obtain ⟨m,hm⟩ := edge 1 (Or.inr rfl)
  exact ⟨n,m,hn,hm⟩

/-- An embedded marked harmonic torus with its aligned C¹ end avoids the
comparison helicoid in the open fundamental disk. This conclusion
includes the compact interior of the surface. -/
theorem marked_first_cell_avoids_helicoid {t α : ℝ} (ht : 0<t) (hα : α≠0)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsClosedEmbedding (harmonicTorusImmersion hX)) (b : ℝ)
    (vertical : ∀ h : ℝ, (![0,0,h] : Fin 3 → ℝ) ∈ range (harmonicTorusImmersion hX))
    (endGraph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b] ∘ harmonicTorusImmersion hX))
    (align : range (axisRuledHelicoid I α b)=range (axisRuledHelicoid I α 0)) :
    ∀ z∈rhombicAxisRectangle (-1) t, X z∉range (axisRuledHelicoid I α b) := by
  obtain ⟨F,cF,rep,_⟩ := marked_torus_closed_cell_phase ht hα hX hE b vertical endGraph
  obtain ⟨n,m,bot,top⟩ := closed_cell_horizontal_phase_constants ht hX hE.injective align cF rep
  let H := rhombicWeightedHeight t X ∘ rhombicCellPoint t
  obtain ⟨cH,sign,nonzero⟩ := marked_closed_cell_height_signs ht hX hE.injective
  have mid {q : unitInterval × unitInterval} (y0 : q.2≠0) (y1 : q.2≠1) :
      (0:ℝ)<q.2 ∧ (q.2:ℝ)<1 := ⟨lt_of_le_of_ne q.2.2.1 (fun e => y0 (Subtype.ext e.symm)),lt_of_le_of_ne q.2.2.2 (fun e => y1 (Subtype.ext e))⟩
  have test (q : unitInterval × unitInterval) (x0 : q.1≠0) (x1 : q.1≠1) (y0 : q.2≠0) (y1 : q.2≠1)
      (hz : H q=0) (k : ℤ) (level : F q=k*Real.pi) : False := by
    let z := rhombicCellPoint t q
    have y := mid y0 y1
    have good := rhombicCell_middle_regular ht q y
    have xx := mid (q := (q.2,q.1)) x0 x1
    have l : -1<z.re := by change -1<(q.1:ℝ)-1; linarith [xx.1]
    have r : z.re<0 := by change (q.1:ℝ)-1<0; linarith [xx.2]
    have re := (cell_relative_phase_im ht hX hE.injective α b good l r (rep _ good)).mp
      (Real.sin_eq_zero_iff.mpr ⟨k,level.symm⟩)
    have height := (rhombicWeightedHeight_zero_iff good X).mp hz
    exact (rhombic_middle_avoids_horizontal_axis ht hX hE.injective q y).1
      ⟨(aligned_relative_horizontal_at_height_zero align _ height).mp re,height⟩
  have result := rectangle_phase_excludes_comparison_leaves H F cH cF sign nonzero n m bot top test
    (marked_closed_cell_phase_no_extrema ht hX hE α b cF rep)
  intro z hz on
  have sz : z∈closedRhombicAxisCell t := ⟨⟨hz.1.1.le,by simpa using hz.1.2.le⟩,⟨hz.2.1.le,hz.2.2.le⟩⟩
  let q := rhombicCellClamp t z
  have ez : rhombicCellPoint t q=z := rhombicCellPoint_clamp ht sz
  have ey : t*(q.2:ℝ)=z.im := congrArg im ez
  have y0 : q.2≠0 := by intro e; rw [e] at ey; simp at ey; linarith [hz.2.1]
  have y1 : q.2≠1 := by intro e; rw [e] at ey; simp at ey; linarith [hz.2.2]
  have gd := (regularClosedRhombicAxisCell_iff ht z).mpr ⟨sz,rhombic_horizontal_strip_not_mem ht hz.2⟩
  have e := rep q (ez.symm ▸ gd)
  rw [ez] at e
  have s := (cell_relative_phase_im ht hX hE.injective α b gd hz.1.1 (by simpa using hz.1.2) e).mpr
    ((relative_horizontal_im_eq_zero_iff α b _).mpr on)
  obtain ⟨k,ek⟩ := Real.sin_eq_zero_iff.mp s
  exact result q y0 y1 k ek.symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.closed_cell_horizontal_phase_constants
#print axioms TwoAxisHelicoid.marked_first_cell_avoids_helicoid
