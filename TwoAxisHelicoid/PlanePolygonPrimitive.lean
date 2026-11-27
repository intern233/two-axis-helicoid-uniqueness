import TwoAxisHelicoid.PuncturedDiskPolygon
import TwoAxisHelicoid.StripPrimitives
import TwoAxisHelicoid.EllipticPrincipalPart

namespace TwoAxisHelicoid
open Complex Metric Filter Set MeasureTheory
open scoped Topology

namespace PlanePolygon

/-- Complex integral of the lifted differential along all the polygon's edges. -/
noncomputable def integral {Ω : Set ℂ} (f : ℂ → ℂ) {x y : ℂ} (p : PlanePolygon Ω x y) : ℂ :=
  match p with
  | .refl _ _ => 0
  | .step a b _ => (b-a) * ∫ s : ℝ in 0..1, f (AffineMap.lineMap (k := ℝ) a b s)
  | .trans p q => p.integral f + q.integral f

end PlanePolygon

/-- Vanishing of complex periods on all polygons which project to closed
paths gives a single-valued holomorphic primitive on the punctured torus. -/
theorem periodic_primitive_of_zero_polygon_periods (L : PeriodPair) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    (hzero : ∀ {x y : ℂ} (p : PlanePolygon (L.lattice : Set ℂ)ᶜ x y),
      y-x ∈ L.lattice → p.integral f = 0) :
    ∃ F : ℂ → ℂ, (∀ z ω, ω ∈ L.lattice → F (z+ω) = F z) ∧
      ∀ z ∉ L.lattice, HasDerivAt F (f z) z := by
  classical
  let Ω := (L.lattice : Set ℂ)ᶜ
  have hopen : IsOpen Ω := L.isClosed_lattice.isOpen_compl
  have hcount : (L.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  have hc := hcount.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ)
  let b := L.ω₁/2
  have hb : b ∈ Ω := L.ω₁_div_two_notMem_lattice
  let path (x y : ℂ) (hx : x ∈ Ω) (hy : y ∈ Ω) : PlanePolygon Ω x y :=
    (planePolygon_exists hopen hc.isPreconnected hx hy).some
  let F (z : ℂ) := if h : z ∈ Ω then (path b z hb h).integral f else 0
  have hincr {x y : ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) (p : PlanePolygon Ω x y) :
      F y = F x + p.integral f := by
    let q := path y b hy hb
    have h1 := hzero ((path b y hb hy).trans q) (by simp)
    have h2 := hzero (((path b x hb hx).trans p).trans q) (by simp)
    simp only [PlanePolygon.integral] at h1 h2
    simp only [F,dite_eq_left hx,dite_eq_left hy]
    linear_combination h1-h2
  refine ⟨F,?_,?_⟩
  · intro z ω hω
    by_cases hz : z ∈ Ω
    · have hz' : z+ω ∈ Ω := fun hn => hz (by simpa using L.lattice.sub_mem hn hω)
      let p := path z (z+ω) hz hz'
      rw [hincr hz hz' p,hzero p (by simpa using hω),add_zero]
    · have h : z ∈ L.lattice := by simpa [Ω] using hz
      have hn : z+ω ∉ Ω := fun he => he (L.lattice.add_mem h hω)
      simp [F,hn,hz]
  · intro z hz
    obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hopen z hz
    let B := ball z r
    have hd : DifferentiableOn ℂ f B :=
      fun w hw => (hf w (hsub hw)).differentiableAt.differentiableWithinAt
    let G (w : ℂ) := wedgeIntegral z w f
    have hG (w : ℂ) (hw : w ∈ B) : HasDerivAt G (f w) w :=
      hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn hw
    have hzb : z ∈ B := mem_ball_self hr
    apply ((hG z hzb).add_const (F z-G z)).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds z hr] with w hw
    have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        AffineMap.lineMap (k := ℝ) z w s ∈ B := (convex_ball z r).lineMap_mem hzb hw hs
    let p := PlanePolygon.step (Ω := Ω) z w (fun s hs => hsub (hseg s hs))
    have h := hincr hz (hsub hw) p
    have he := primitive_path_integral_eq_sub (γ := AffineMap.lineMap (k := ℝ) z w)
      (F := G) (f := f) (a := 0) (b := 1)
      (fun _ _ => AffineMap.hasDerivAt_lineMap)
      (fun s hs => hG _ (hseg s (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs)))
      ((show ContinuousOn (fun s : ℝ => f (AffineMap.lineMap (k := ℝ) z w s)) (Icc 0 1)
        from fun s hs => ((hf _ (hsub (hseg s hs))).continuousAt.comp
          AffineMap.lineMap_continuous.continuousAt).continuousWithinAt).intervalIntegrable_of_Icc (by norm_num))
    simp only [AffineMap.lineMap_apply_one,AffineMap.lineMap_apply_zero] at he
    change F w = G w+(F z-G z)
    change F w = F z+((w-z)*_) at h
    linear_combination h+he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodic_primitive_of_zero_polygon_periods
