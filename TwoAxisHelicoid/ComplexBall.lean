import TwoAxisHelicoid.ExpEnclosure

/-!
Exact rational complex disks. Each operation is linked to the actual complex
field; optional outward coarsening can keep generated certificates small.
-/

namespace TwoAxisHelicoid

structure QComplex where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

namespace QComplex

noncomputable def val (c : QComplex) : ℂ := ⟨c.re, c.im⟩
def ofRat (q : ℚ) : QComplex := ⟨q, 0⟩
def add (c d : QComplex) : QComplex := ⟨c.re+d.re, c.im+d.im⟩
def neg (c : QComplex) : QComplex := ⟨-c.re, -c.im⟩
def sub (c d : QComplex) : QComplex := add c (neg d)
def mul (c d : QComplex) : QComplex := ⟨c.re*d.re-c.im*d.im, c.re*d.im+c.im*d.re⟩
def inv (c : QComplex) : QComplex :=
  ⟨c.re/(c.re^2+c.im^2), -c.im/(c.re^2+c.im^2)⟩
def absUpper (c : QComplex) : ℚ := |c.re|+|c.im|
def absLower (c : QComplex) : ℚ := max |c.re| |c.im|

@[simp] theorem val_ofRat (q : ℚ) : (ofRat q).val = (q : ℂ) := by
  apply Complex.ext <;> simp [val, ofRat]

@[simp] theorem val_add (c d : QComplex) : (add c d).val = c.val+d.val := by
  apply Complex.ext <;> simp [val, add]

@[simp] theorem val_neg (c : QComplex) : (neg c).val = -c.val := by
  apply Complex.ext <;> simp [val, neg]

@[simp] theorem val_sub (c d : QComplex) : (sub c d).val = c.val-d.val := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem val_mul (c d : QComplex) : (mul c d).val = c.val*d.val := by
  apply Complex.ext <;> simp [val, mul]

@[simp] theorem val_inv (c : QComplex) : (inv c).val = c.val⁻¹ := by
  apply Complex.ext <;> simp [val, inv, Complex.inv_re, Complex.inv_im, Complex.normSq_apply, pow_two]

theorem norm_val_le (c : QComplex) : ‖c.val‖ ≤ (c.absUpper : ℝ) := by
  simpa [val, absUpper] using Complex.norm_le_abs_re_add_abs_im c.val

theorem absLower_le_norm (c : QComplex) : (c.absLower : ℝ) ≤ ‖c.val‖ := by
  have hr := Complex.abs_re_le_norm c.val
  have hi := Complex.abs_im_le_norm c.val
  simpa [val, absLower] using max_le hr hi

theorem absUpper_nonneg (c : QComplex) : 0 ≤ c.absUpper := by
  unfold absUpper
  positivity

end QComplex

structure ComplexBall where
  center : QComplex
  radius : ℚ
  deriving DecidableEq, Repr

namespace ComplexBall

def Contains (b : ComplexBall) (z : ℂ) : Prop := ‖z-b.center.val‖ ≤ (b.radius : ℝ)

def point (c : QComplex) : ComplexBall := ⟨c, 0⟩
def add (a b : ComplexBall) : ComplexBall := ⟨a.center.add b.center, a.radius+b.radius⟩
def neg (a : ComplexBall) : ComplexBall := ⟨a.center.neg, a.radius⟩
def sub (a b : ComplexBall) : ComplexBall := add a (neg b)
def mul (a b : ComplexBall) : ComplexBall :=
  ⟨a.center.mul b.center,
    a.center.absUpper*b.radius+b.center.absUpper*a.radius+a.radius*b.radius⟩
def lower (a : ComplexBall) : ℚ := a.center.absLower-a.radius
def inv (a : ComplexBall) : ComplexBall :=
  ⟨a.center.inv, a.center.inv.absUpper*a.radius/a.lower⟩

def pow (a : ComplexBall) : ℕ → ComplexBall
  | 0 => point (QComplex.ofRat 1)
  | n+1 => mul (pow a n) a

def coarsens (b a : ComplexBall) : Prop :=
  (a.center.sub b.center).absUpper+a.radius ≤ b.radius

instance (b a : ComplexBall) : Decidable (coarsens b a) := inferInstanceAs
  (Decidable ((a.center.sub b.center).absUpper+a.radius ≤ b.radius))

theorem radius_nonneg {a : ComplexBall} {z : ℂ} (ha : a.Contains z) : 0 ≤ a.radius := by
  exact_mod_cast (norm_nonneg (z-a.center.val)).trans ha

theorem point_contains (c : QComplex) : (point c).Contains c.val := by
  simp [Contains, point]

theorem add_contains {a b : ComplexBall} {z w : ℂ} (ha : a.Contains z) (hb : b.Contains w) :
    (add a b).Contains (z+w) := by
  unfold Contains add
  simp only [QComplex.val_add, Rat.cast_add]
  calc
    _ = ‖(z-a.center.val)+(w-b.center.val)‖ := by congr 1; ring
    _ ≤ ‖z-a.center.val‖+‖w-b.center.val‖ := norm_add_le _ _
    _ ≤ _ := add_le_add ha hb

theorem neg_contains {a : ComplexBall} {z : ℂ} (ha : a.Contains z) :
    (neg a).Contains (-z) := by
  unfold Contains neg
  rw [QComplex.val_neg, show -z - -a.center.val = -(z-a.center.val) by ring, norm_neg]
  exact ha

theorem sub_contains {a b : ComplexBall} {z w : ℂ} (ha : a.Contains z) (hb : b.Contains w) :
    (sub a b).Contains (z-w) := by
  simpa only [sub, sub_eq_add_neg] using add_contains ha (neg_contains hb)

theorem mul_contains {a b : ComplexBall} {z w : ℂ} (ha : a.Contains z) (hb : b.Contains w) :
    (mul a b).Contains (z*w) := by
  have har : (0 : ℝ) ≤ a.radius := by exact_mod_cast radius_nonneg ha
  have hbr : (0 : ℝ) ≤ b.radius := by exact_mod_cast radius_nonneg hb
  have hac := a.center.norm_val_le
  have hbc := b.center.norm_val_le
  change ‖z-a.center.val‖ ≤ (a.radius : ℝ) at ha
  change ‖w-b.center.val‖ ≤ (b.radius : ℝ) at hb
  unfold Contains mul
  simp only [QComplex.val_mul, Rat.cast_add, Rat.cast_mul]
  calc
    _ = ‖(z-a.center.val)*(w-b.center.val) +
        a.center.val*(w-b.center.val) + (z-a.center.val)*b.center.val‖ := by congr 1; ring
    _ ≤ ‖(z-a.center.val)*(w-b.center.val)‖ +
        ‖a.center.val*(w-b.center.val)‖ + ‖(z-a.center.val)*b.center.val‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (a.radius : ℝ)*b.radius + a.center.absUpper*b.radius + a.radius*b.center.absUpper := by
      simp only [norm_mul]
      exact add_le_add (add_le_add (mul_le_mul ha hb (norm_nonneg _) har)
        (mul_le_mul hac hb (norm_nonneg _) (by exact_mod_cast a.center.absUpper_nonneg)))
        (mul_le_mul ha hbc (norm_nonneg _) har)
    _ = _ := by ring

theorem pow_contains {a : ComplexBall} {z : ℂ} (ha : a.Contains z) (n : ℕ) :
    (pow a n).Contains (z^n) := by
  induction n with
  | zero => simpa [pow, QComplex.val_ofRat] using point_contains (QComplex.ofRat 1)
  | succ n ih => simpa only [pow, pow_succ] using mul_contains ih ha

theorem coarsen_contains {a b : ComplexBall} {z : ℂ} (ha : a.Contains z)
    (hab : coarsens b a) : b.Contains z := by
  have hrat : ((a.center.sub b.center).absUpper : ℝ)+a.radius ≤ b.radius := by exact_mod_cast hab
  have hc := (a.center.sub b.center).norm_val_le
  simp only [QComplex.val_sub] at hc
  unfold Contains at *
  have hn := norm_add_le (z-a.center.val) (a.center.val-b.center.val)
  rw [sub_add_sub_cancel] at hn
  linarith

theorem norm_le {a : ComplexBall} {z : ℂ} (ha : a.Contains z) :
    ‖z‖ ≤ (a.center.absUpper+a.radius : ℚ) := by
  have hn := norm_add_le (z-a.center.val) a.center.val
  have hc := a.center.norm_val_le
  change ‖z-a.center.val‖ ≤ (a.radius : ℝ) at ha
  push_cast
  rw [sub_add_cancel] at hn
  exact hn.trans (by linarith [ha])

theorem lower_le_norm {a : ComplexBall} {z : ℂ} (ha : a.Contains z) :
    (a.lower : ℝ) ≤ ‖z‖ := by
  have hn := norm_add_le (a.center.val-z) z
  have hc := a.center.absLower_le_norm
  rw [sub_add_cancel, norm_sub_rev a.center.val z] at hn
  change ‖z-a.center.val‖ ≤ (a.radius : ℝ) at ha
  unfold lower
  push_cast
  linarith [ha]

theorem ne_zero_of_lower_pos {a : ComplexBall} {z : ℂ} (ha : a.Contains z) (hl : 0 < a.lower) :
    z ≠ 0 := by
  have hlr : (0 : ℝ) < a.lower := by exact_mod_cast hl
  exact norm_pos_iff.mp (hlr.trans_le (lower_le_norm ha))

theorem inv_contains {a : ComplexBall} {z : ℂ} (ha : a.Contains z) (hl : 0 < a.lower) :
    (inv a).Contains z⁻¹ := by
  have hz := ne_zero_of_lower_pos ha hl
  have har : (0 : ℝ) ≤ a.radius := by exact_mod_cast radius_nonneg ha
  have hlr : (0 : ℝ) < a.lower := by exact_mod_cast hl
  have hc : a.center.val ≠ 0 := by
    apply norm_pos_iff.mp
    have hcl := a.center.absLower_le_norm
    have hlow : (0 : ℝ) < a.center.absLower := by
      have hh : (a.lower : ℝ) = a.center.absLower-a.radius := by simp [lower]
      linarith
    exact hlow.trans_le hcl
  have hi : ‖z⁻¹‖ ≤ (a.lower : ℝ)⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hlr (lower_le_norm ha)
  have hci := a.center.inv.norm_val_le
  simp only [QComplex.val_inv] at hci
  unfold Contains inv
  simp only [QComplex.val_inv, Rat.cast_div, Rat.cast_mul]
  calc
    _ = ‖a.center.val⁻¹ * (a.center.val-z) * z⁻¹‖ := by
      congr 1
      field_simp
    _ = ‖a.center.val⁻¹‖ * ‖a.center.val-z‖ * ‖z⁻¹‖ := by simp only [norm_mul]
    _ ≤ (a.center.inv.absUpper : ℝ)*a.radius*(a.lower : ℝ)⁻¹ := by
      rw [norm_sub_rev a.center.val z]
      have hu : (0 : ℝ) ≤ a.center.inv.absUpper := by
        exact_mod_cast a.center.inv.absUpper_nonneg
      exact mul_le_mul (mul_le_mul hci ha (norm_nonneg _) hu) hi
        (norm_nonneg _) (mul_nonneg hu har)
    _ = _ := by rw [div_eq_mul_inv]

end ComplexBall
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ComplexBall.inv_contains
