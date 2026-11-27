import TwoAxisHelicoid.CertificateSemantics
import TwoAxisHelicoid.PeriodConclusion
import TwoAxisHelicoid.LeftSignAll
import TwoAxisHelicoid.PdfRootUniformVertical
import TwoAxisHelicoid.VerticalBranchContinuity
import TwoAxisHelicoid.RootVerticalConstants

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000

/-- The two uniform vertical cuts in the root attachment bound the
abscissa for every height in the full closed interval. -/
theorem raw_root_uniform_abscissa {t : ℝ} (bounds : t∈Icc (rootTLower:ℝ) rootTUpper) :
    verticalA t∈Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
      (4409686737857433550400689051219/7427640235712281649394745344000) := by
  have tl : ((54139230899/62500000000:ℚ):ℝ)≤t := by
    convert bounds.1 using 1
    norm_num [rootTLower]
  have tu : t≤((173245538877/200000000000:ℚ):ℝ) := by
    convert bounds.2 using 1
    norm_num [rootTUpper]
  obtain ⟨lv,uv⟩ := pdf_root_uniform_vertical_bounds tl tu
  let l : ℝ := ((4409686737850678150959633307219/7427640235712281649394745344000:ℚ):ℝ)
  let u : ℝ := ((4409686737857433550400689051219/7427640235712281649394745344000:ℚ):ℝ)
  have hl : l∈Ioo (0:ℝ) 1 := by norm_num [l]
  have hu : u∈Ioo (0:ℝ) 1 := by norm_num [u]
  have pos : 0<(thetaG t l).re := lt_of_lt_of_le (by norm_num) lv.1
  have neg : (thetaG t u).re<0 := lt_of_le_of_lt uv.2 (by norm_num)
  have t0 : 0<t := lt_of_lt_of_le (by norm_num) tl
  obtain ⟨inside,zero⟩ := verticalA_spec ⟨t0,tu.trans_lt ((by norm_num : ((173245538877/200000000000:ℚ):ℝ)<100000000/70945980).trans ellipticVerticalUpper_location.1)⟩
  have zr : (thetaG t (verticalA t)).re=0 := by rw [zero];rfl
  have anti := (thetaG_strictAnti_unit_of_pos t0).antitoneOn
  have ab : l<verticalA t ∧ verticalA t<u := by
    constructor
    · by_contra! h
      have v := anti inside hl h
      change (thetaG t l).re≤(thetaG t (verticalA t)).re at v
      linarith
    · by_contra! h
      have v := anti hu inside h
      change (thetaG t (verticalA t)).re≤(thetaG t u).re at v
      linarith
  simpa only [l,u,Rat.cast_div,Rat.cast_ofNat,Set.mem_Ioo] using ab

/-- The positive, negative, derivative and right-end columns of the PDF
imply all five sign hypotheses on the actual scalar period. -/
theorem raw_tables_period_hypotheses
    (pos : ∀ r∈positiveData, ∀ t : ℝ, RealMem r.t t → RealMem r.hReal (actualPeriodAlong t))
    (neg : ∀ r∈negativeData, ∀ t : ℝ, RealMem r.t t → RealMem r.hReal (actualPeriodAlong t))
    (heat : ∀ r∈derivativeData, ∀ t : ℝ, RealMem r.t t → deriv actualPeriodAlong t≤(r.hPrimeUpper:ℝ))
    (right : ∀ r∈endpointData, ∀ t a : ℝ, (7/5:ℝ)≤t → t≤141/100 → RealMem r.a a →
      thetaHorizontalPeriod t a≤(r.hUpper:ℝ))
    (cut : ∀ t : ℝ, 7/5≤t → t≤141/100 → t<ellipticVerticalUpper → 9/10<verticalA t ∧ verticalA t<1) :
    PeriodHypotheses actualPeriodAlong ellipticVerticalUpper := by
  have T := ellipticVerticalUpper_location
  refine ⟨(by norm_num : (7/5:ℝ)<100000000/70945980).trans T.1,
    actualPeriodAlong_continuousOn.mono (fun _ ht => ⟨by linarith [ht.1],by linarith [ht.2,T.1]⟩),
    fun _ ht => actualPeriodAlong_positive_left ht.1 ht.2,
    fun _ ht => pdf_positive_of_enclosures _ pos ht,
    fun _ ht => pdf_negative_of_enclosures _ neg ht,?_,?_⟩
  · intro t ht
    have tu := ht.2.le.trans (T.2.le.trans (by norm_num : (100000000/70945978:ℝ)≤141/100))
    obtain ⟨al,au⟩ := cut t ht.1 tu ht.2
    obtain ⟨I,hi,mem⟩ := partition_covers endpoint_partition (by norm_num) (x:=verticalA t)
      (by simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,div_one] using And.intro al.le au.le)
    obtain ⟨r,member,rfl⟩ := List.mem_map.mp hi
    exact (right r member t (verticalA t) ht.1 tu mem).trans_lt
      (by simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr r.verified.2.2.2)
  · intro t ht
    obtain ⟨I,hi,mem⟩ := partition_covers derivative_partition (by norm_num) (x:=t)
      (by simpa only [Rat.cast_div,Rat.cast_ofNat,Set.mem_Icc] using ht)
    obtain ⟨r,member,rfl⟩ := List.mem_map.mp hi
    exact (heat r member t mem).trans_lt (by exact_mod_cast r.verified.2.2.2.2.2.2)

/-- The root endpoints and the original derivative row containing their
entire closed interval imply the precise location and simplicity in 10.1. -/
theorem raw_root_signs_give_location (period : PeriodHypotheses actualPeriodAlong ellipticVerticalUpper)
    (heat : ∀ r∈derivativeData, ∀ t : ℝ, RealMem r.t t → deriv actualPeriodAlong t≤(r.hPrimeUpper:ℝ))
    (left : 0<actualPeriodAlong rootTLower) (right : actualPeriodAlong rootTUpper<0)
    {t : ℝ} (dom : t∈Ioo (0:ℝ) ellipticVerticalUpper) (zero : actualPeriodAlong t=0) :
    t∈Ioo (rootTLower:ℝ) rootTUpper ∧
      verticalA t∈Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧ deriv actualPeriodAlong t< -8 := by
  have within := localize_period_zero_of_hypotheses period
    (by norm_num [rootTLower,Set.mem_Icc]) (by norm_num [rootTUpper,Set.mem_Icc]) left right dom zero
  have member : derivative_016∈derivativeData := List.getElem_mem (l:=derivativeData) (n:=16) (by decide)
  have inside : RealMem derivative_016.t t := by
    constructor
    · exact le_trans (by norm_num [derivative_016,rootTLower]) within.1.le
    · exact le_trans within.2.le (by norm_num [derivative_016,rootTUpper])
  exact ⟨within,raw_root_uniform_abscissa ⟨within.1.le,within.2.le⟩,
    (heat _ member _ inside).trans_lt (by norm_num [derivative_016])⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.raw_root_uniform_abscissa
#print axioms TwoAxisHelicoid.PdfVertical.raw_root_signs_give_location

