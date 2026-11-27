import TwoAxisHelicoid.VanishingCircleDoublePole
import TwoAxisHelicoid.PrimitiveDoublePoleExpansion
import TwoAxisHelicoid.PuncturedGaussLogFactorization

namespace TwoAxisHelicoid
open Complex Set Filter Metric MeasureTheory
open scoped Topology

/-- A single-valued primitive of a genuine double-pole differential
has a genuine simple pole. The circle periods needed to eliminate the
residue follow from the given primitive. -/
theorem primitive_simple_pole_of_double_differential {f F : ℂ → ℂ}
    (mer : MeromorphicAt f 0) (order : meromorphicOrderAt f 0=(-2:ℤ))
    (dF : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (f z) z) :
    MeromorphicAt F 0 ∧ meromorphicOrderAt F 0=(-1:ℤ) := by
  obtain ⟨r,rp,good⟩ := Metric.mem_nhdsWithin_iff.mp dF
  have circles (R : ℝ) (Rp : 0<R) : ∃ s∈Ioo (0:ℝ) R, (∮ z in C(0,s), f z)=0 := by
    let s := min r R/2
    have sp : 0<s := half_pos (lt_min rp Rp)
    have sr : s<r := (half_lt_self (lt_min rp Rp)).trans_le (min_le_left _ _)
    have sR : s<R := (half_lt_self (lt_min rp Rp)).trans_le (min_le_right _ _)
    refine ⟨s,⟨sp,sR⟩,circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f:=F) sp.le ?_⟩
    intro z hz
    have rad : ‖z‖=s := by simpa only [mem_sphere,dist_zero_right] using hz
    exact (good (show z∈ball (0:ℂ) r ∩ {0}ᶜ from ⟨mem_ball_zero_iff.mpr (rad.trans_lt sr),
      norm_pos_iff.mp (rad.symm ▸ sp)⟩)).hasDerivWithinAt
  obtain ⟨A,P,nz,an,main⟩ := double_pole_principal_part_of_zero_circle_periods mer order circles
  obtain ⟨G,ga,rest⟩ := primitive_of_double_pole_expansion (F:=F) an
    (eventually_nhdsWithin_iff.mp ((dF.and main).mono (fun z hz => hz.2 ▸ hz.1)))
  have eq : F =ᶠ[𝓝[≠] (0:ℂ)] fun z => (-A)/z+G z := eventually_nhdsWithin_iff.mpr rest
  have mF : MeromorphicAt F 0 := (((MeromorphicAt.const (-A) 0).div analyticAt_id.meromorphicAt).add ga.meromorphicAt).congr eq.symm
  let U := fun z : ℂ => -A+z*G z
  refine ⟨mF,(meromorphicOrderAt_eq_int_iff mF).mpr ⟨U,analyticAt_const.add (analyticAt_id.mul ga),by simpa [U] using nz,?_⟩⟩
  filter_upwards [eq,self_mem_nhdsWithin] with z hz non
  change z≠0 at non
  simp only [sub_zero,zpow_neg_one,smul_eq_mul,U,hz]
  field_simp [non]

/-- In any genuine puncture chart where the physical height and the
logarithmic Gauss differential both have double poles, a height primitive
and the single-valued factor of the Gauss logarithm both have simple poles.
No genus or symmetry assumptions are used. -/
theorem logarithmic_factors_of_measured_double_poles {h g H : ℂ → ℂ}
    (hm : MeromorphicAt h 0) (ho : meromorphicOrderAt h 0=(-2:ℤ))
    (gm : MeromorphicAt (logDeriv g) 0) (go : meromorphicOrderAt (logDeriv g) 0=(-2:ℤ))
    (reg : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ g z ∧ g z≠0)
    (dH : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (h z) z) :
    MeromorphicAt H 0 ∧ meromorphicOrderAt H 0=(-1:ℤ) ∧
      ∃ (n : ℤ) (F : ℂ → ℂ), MeromorphicAt F 0 ∧ meromorphicOrderAt F 0=(-1:ℤ) ∧
        ∀ᶠ z in 𝓝[≠] (0:ℂ), g z=z^n*exp (F z) := by
  obtain ⟨hmem,hord⟩ := primitive_simple_pole_of_double_differential hm ho dH
  obtain ⟨r,rp,good⟩ := Metric.mem_nhdsWithin_iff.mp reg
  obtain ⟨n,F,fac⟩ := punctured_holomorphic_unit_factor (g:=g) rp (fun z p s =>
    good (show z∈ball (0:ℂ) r ∩ {0}ᶜ from ⟨mem_ball_zero_iff.mpr s,norm_pos_iff.mp p⟩))
  have factors : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (logDeriv g z-(n:ℂ)/z) z ∧ g z=z^n*exp (F z) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) rp)] with z nz sm
    exact fac z (norm_pos_iff.mpr nz) (mem_ball_zero_iff.mp sm)
  let k := fun z : ℂ => (n:ℂ)/z
  have km : MeromorphicAt k 0 := (MeromorphicAt.const (n:ℂ) 0).div analyticAt_id.meromorphicAt
  have smaller : meromorphicOrderAt (logDeriv g) 0<meromorphicOrderAt (-k) 0 := by
    rw [← meromorphicOrderAt_neg (f:=k),go]
    by_cases nz : (n:ℂ)=0
    · have ke : k=fun _ : ℂ => (0:ℂ) := by funext z; simp [k,nz]
      rw [ke,meromorphicOrderAt_const]
      simp only [↓reduceIte]
      exact WithTop.coe_lt_top _
    · change _<meromorphicOrderAt ((fun _ : ℂ => (n:ℂ))/(id : ℂ → ℂ)) 0
      rw [meromorphicOrderAt_div (MeromorphicAt.const (n:ℂ) 0) analyticAt_id.meromorphicAt,meromorphicOrderAt_const,meromorphicOrderAt_id]
      simp only [nz,↓reduceIte]
      exact WithTop.coe_lt_coe.mpr (by decide : (-2:ℤ)<0-1)
  have ord : meromorphicOrderAt (logDeriv g-k) 0=(-2:ℤ) := by
    rw [sub_eq_add_neg,meromorphicOrderAt_add_eq_left_of_lt km.neg smaller,go]
  obtain ⟨fm,fo⟩ := primitive_simple_pole_of_double_differential (gm.sub km) ord (factors.mono fun _ p => p.1)
  exact ⟨hmem,hord,n,F,fm,fo,factors.mono fun _ p => p.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.primitive_simple_pole_of_double_differential
#print axioms TwoAxisHelicoid.logarithmic_factors_of_measured_double_poles
