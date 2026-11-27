import TwoAxisHelicoid.LowSlabEdgeSound
import TwoAxisHelicoid.RectangleRealPartBound

namespace TwoAxisHelicoid
open Complex Set

/-- Both limiting directions and every direction between them are
controlled throughout the rectangle by holomorphic comparison. -/
theorem low_slab_sector_rectangle {a b c d : ℚ} (ab : a≤b) (cd : c≤d)
    (xl : 0≤a) (xr : b≤1) (yb : 0≤c) (yt : d≤7/16)
    (left : CheckedLowSlabEdge .sector true a c d) (right : CheckedLowSlabEdge .sector true b c d)
    (bottom : CheckedLowSlabEdge .sector false c a b) (top : CheckedLowSlabEdge .sector false d a b) :
    let p := certifiedClosedParameters
    ∀ x∈Icc (a:ℝ) b, ∀ y∈Icc (c:ℝ) d, ∀ u : ℝ, |u|≤1 →
      let F := centralPhaseThetaRatio p.t p.a ⟨x,y⟩
      4*F.re+u*F.im<0 := by
  intro p x hx y hy u hu
  let R := centralPhaseThetaRatio p.t p.a
  let g := fun z : ℂ => -(⟨4,-u⟩*R z)
  have tall : (7/16:ℝ)<p.t := by have q := certifiedClosedParameters_bounds.1.1; norm_num [rootTLower] at q; linarith
  have diff (z : ℂ) (xx : z.re∈Icc (a:ℝ) b) (yy : z.im∈Icc (c:ℝ) d) : DifferentiableAt ℂ g z := by
    have xmin : 0≤z.re := (by exact_mod_cast xl : (0:ℝ)≤a).trans xx.1
    have xmax : z.re≤1 := xx.2.trans (by exact_mod_cast xr)
    have ymin : 0≤z.im := (by exact_mod_cast yb : (0:ℝ)≤c).trans yy.1
    have ymax : z.im<p.t := yy.2.trans_lt ((by simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr yt : (d:ℝ)≤7/16).trans_lt tall)
    have off : z+p.a∉(rhombicPeriodPair p.t p.height_pos).lattice := by
      rcases ymin.eq_or_lt with e|pos
      · have same : z+p.a=((z.re+p.a:ℝ):ℂ) := by apply Complex.ext <;> simp [e.symm]
        rw [same]
        exact real_not_mem_rhombic_lattice_of_pos p.height_pos (by linarith [p.abscissa_mem.1]) (by linarith [p.abscissa_mem.2])
      · exact rhombic_horizontal_strip_not_mem p.height_pos (by change (z+(p.a:ℂ)).im∈Ioo 0 p.t; simpa using And.intro pos ymax)
    exact ((centralPhaseThetaRatio_analyticAt p.height_pos off).differentiableAt.const_mul (⟨4,-u⟩:ℂ)).neg
  have form (z : ℂ) : (g z).re= -(4*(R z).re+u*(R z).im) := by simp [g,Complex.mul_re]
  let m := (1/1024:ℝ)
  have edge {v : Bool} {p l r : ℚ} (cert : CheckedLowSlabEdge .sector v p l r) (x : ℝ) (xx : x∈Icc (l:ℝ) r) :
      m≤(g (centralBandEdgePoint v p x)).re := by
    have bound := cert.sound x xx u hu
    rw [form]
    change 4*(R (centralBandEdgePoint v p x)).re+u*(R (centralBandEdgePoint v p x)).im≤ -(1/1024:ℝ) at bound
    dsimp only [m]
    linarith
  have value := rectangle_real_lower_bound (f:=g) (m:=m) (by exact_mod_cast ab : (a:ℝ)≤b)
    (by exact_mod_cast cd : (c:ℝ)≤d) diff (fun s hs k hk => by
      rcases (show s=(a:ℝ) ∨ s=(b:ℝ) by simpa only [mem_insert_iff,mem_singleton_iff] using hs) with rfl|rfl
      · exact edge left k hk
      · exact edge right k hk) (fun s hs k hk => by
      rcases (show s=(c:ℝ) ∨ s=(d:ℝ) by simpa only [mem_insert_iff,mem_singleton_iff] using hs) with rfl|rfl
      · exact edge bottom k hk
      · exact edge top k hk) ⟨x,y⟩ hx hy
  rw [form] at value
  change 4*(R ⟨x,y⟩).re+u*(R ⟨x,y⟩).im<0
  dsimp only [m] at value
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_slab_sector_rectangle
