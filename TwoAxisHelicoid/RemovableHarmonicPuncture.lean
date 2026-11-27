import TwoAxisHelicoid.SurfaceHarmonicComparison
import TwoAxisHelicoid.PoissonDiskBoundary
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function InnerProductSpace
open scoped Topology

/-- A bounded-above harmonic function on a punctured disk obeys
the maximum principle using only its outer boundary. The logarithmic
barrier controls the newly introduced inner circle. -/
theorem bounded_harmonic_punctured_disk_maximum {u : ℂ → ℝ} {c : ℂ} {r C : ℝ} (_rp : 0<r)
    (cu : ContinuousOn u (closedBall c r \ {c})) (hu : HarmonicOnNhd u (ball c r \ {c}))
    (bound : ∀ z∈closedBall c r \ {c}, u z≤C) (edge : ∀ z∈sphere c r, u z≤0) :
    ∀ z∈closedBall c r \ {c}, u z≤0 := by
  intro w hw
  by_contra! pos
  have dpos : 0<dist w c := dist_pos.mpr hw.2
  let k := Real.log (dist w c)-Real.log r
  have small : ∀ᶠ a : ℝ in 𝓝 0, 0<u w+a*k := by
    have cc : Continuous (fun a : ℝ => u w+a*k) := by fun_prop
    exact cc.continuousAt.eventually (lt_mem_nhds (by simpa using pos))
  have right : ∀ᶠ a : ℝ in 𝓝[>] 0, 0<a := self_mem_nhdsWithin
  obtain ⟨a,ap,aw⟩ := (right.and (small.filter_mono nhdsWithin_le_nhds)).exists
  let δ := min (dist w c/2) (Real.exp (Real.log r-(|C|+1)/a))
  have dp : 0<δ := lt_min (half_pos dpos) (Real.exp_pos _)
  have dw : δ<dist w c := (min_le_left _ _).trans_lt (half_lt_self dpos)
  have logδ : Real.log δ≤Real.log r-(|C|+1)/a := by
    rw [← Real.log_exp (Real.log r-(|C|+1)/a)]
    exact Real.log_le_log dp (min_le_right _ _)
  let K := closedBall c r \ ball c δ
  let v := fun z => u z+a*(Real.log (dist z c)-Real.log r)
  have d (z : ℂ) (hz : z∈K) : δ≤dist z c := le_of_not_gt hz.2
  have original (z : ℂ) (hz : z∈K) : z∈closedBall c r \ {c} := ⟨hz.1,dist_pos.mp (dp.trans_le (d z hz))⟩
  have outer (z : ℂ) (hz : z∈sphere c r) : v z≤0 := by simpa [v,mem_sphere.mp hz] using edge z hz
  have inner (z : ℂ) (hz : z∈K) (eq : dist z c=δ) : v z≤0 := by
    have lm := mul_le_mul_of_nonneg_left logδ ap.le
    have cancel : a*((|C|+1)/a)=|C|+1 := by field_simp
    change u z+a*(Real.log (dist z c)-Real.log r)≤0
    rw [eq]
    nlinarith [bound z (original z hz),le_abs_self C]
  have ck : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have cv : ContinuousOn v K := (cu.mono original).add (continuousOn_const.mul
    (((continuous_id.dist continuous_const).continuousOn.log fun z hz => (dp.trans_le (d z hz)).ne').sub continuousOn_const))
  have op : IsOpen {z : ℂ | δ<dist z c ∧ dist z c<r} :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter isOpen_ball
  have sub : {z : ℂ | δ<dist z c ∧ dist z c<r}⊆K := fun _ h => ⟨h.2.le,not_lt.mpr h.1.le⟩
  have mx := compact_boundary_maximum_principle ck cv (fun z hz out => by
    rcases (d z hz).eq_or_lt with eq|gt
    · exact inner z hz eq.symm
    rcases (mem_closedBall.mp hz.1).lt_or_eq with lt|eq
    · exact (out (mem_interior_iff_mem_nhds.mpr (mem_of_superset (op.mem_nhds ⟨gt,lt⟩) sub))).elim
    · exact outer z eq) (fun z hz high loc => by
    have mem := interior_subset hz
    have n := original z mem
    have lt : dist z c<r := lt_of_le_of_ne (mem_closedBall.mp mem.1) (fun eq => high.not_ge (outer z eq))
    have harm : HarmonicAt (fun q : ℂ => Real.log (dist q c)) z := by
      have an : AnalyticAt ℂ (fun t : ℂ => t-c) z := analyticAt_id.sub analyticAt_const
      simpa only [dist_eq_norm] using an.harmonicAt_log_norm (sub_ne_zero.mpr n.2)
    apply harmonic_eventually_constant_at_local_max _ loc
    exact (hu z ⟨lt,n.2⟩).add ((harm.sub (harmonicAt_const (c:=Real.log r))).const_smul (c:=a)))
  exact (show 0<v w from aw).not_ge (mx w ⟨hw.1,not_lt.mpr dw.le⟩)

/-- Every bounded harmonic function on a punctured neighborhood has
a harmonic extension across the puncture, agreeing as a punctured germ. -/
theorem bounded_harmonic_puncture_removable {u : ℂ → ℝ} {c : ℂ}
    (harm : ∀ᶠ z in 𝓝[≠] c, HarmonicAt u z) {C : ℝ} (bound : ∀ᶠ z in 𝓝[≠] c, |u z|≤C) :
    ∃ v : ℂ → ℝ, HarmonicAt v c ∧ u =ᶠ[𝓝[≠] c] v := by
  obtain ⟨s,sn,sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (harm.and bound)
  obtain ⟨r,rp,cr⟩ := Metric.nhds_basis_closedBall.mem_iff.mp sn
  have info (z : ℂ) (hz : z∈closedBall c r \ {c}) : HarmonicAt u z ∧ |u z|≤C := sub ⟨cr hz.1,hz.2⟩
  have ct : ContinuousOn u (closedBall c r \ {c}) := fun z hz => (info z hz).1.1.continuousAt.continuousWithinAt
  have circ : sphere c r⊆closedBall c r \ {c} := fun z hz => ⟨sphere_subset_closedBall hz,dist_pos.mp ((mem_sphere.mp hz).symm ▸ rp)⟩
  obtain ⟨v,hv,cv,eq⟩ := continuous_disk_dirichlet_solution rp (ct.mono circ)
  obtain ⟨D,bd⟩ := ((isCompact_closedBall c r).image_of_continuousOn cv).isBounded.exists_norm_le
  have bv (z : ℂ) (hz : z∈closedBall c r) : |v z|≤D := bd _ (mem_image_of_mem v hz)
  have comp (z : ℂ) (hz : z∈ball c r \ {c}) := info z ⟨ball_subset_closedBall hz.1,hz.2⟩
  have ctv := cv.mono (sdiff_subset (t:={c}))
  have above := bounded_harmonic_punctured_disk_maximum (C:=C+D) rp (ct.sub ctv)
    (fun z hz => (comp z hz).1.sub (hv z hz.1))
    (fun z hz => by dsimp; linarith [(abs_le.mp (info z hz).2).2,(abs_le.mp (bv z hz.1)).1])
    (fun z hz => by simp [eq hz])
  have below := bounded_harmonic_punctured_disk_maximum (C:=C+D) rp (ctv.sub ct)
    (fun z hz => (hv z hz.1).sub (comp z hz).1)
    (fun z hz => by dsimp; linarith [(abs_le.mp (info z hz).2).1,(abs_le.mp (bv z hz.1)).2])
    (fun z hz => by simp [eq hz])
  refine ⟨v,hv c (mem_ball_self rp),?_⟩
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds c rp)] with z ne hz
  exact le_antisymm (sub_nonpos.mp (above z ⟨hz,ne⟩)) (sub_nonpos.mp (below z ⟨hz,ne⟩))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_harmonic_puncture_removable
