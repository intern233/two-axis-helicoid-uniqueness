module

public import TwoAxisHelicoid.VerticalRunCoreTests

@[expose] public section
namespace TwoAxisHelicoid.VerticalAttachment
open VerticalRunCore (sumPrefix factorial)

abbrev Box := Rat × Rat
def decimalScale : Rat := 10^30

/-- The attachment rounds each arithmetic interval to the decimal grid. -/
def outward (lo hi : Rat) : Box :=
  (((lo*decimalScale).floor : Rat)/decimalScale,
   ((hi*decimalScale).ceil : Rat)/decimalScale)

def atanBox (x : Rat) : Box :=
  let lo := sumPrefix (fun j => (-1 : Rat)^j * x^(2*j+1) / (2*(j : Rat)+1)) 40
  (lo, lo + x^81/81)

def piBox : Box :=
  let a := atanBox (1/5)
  let b := atanBox (1/239)
  outward (16*a.1-4*b.2) (16*a.2-4*b.1)

def taylor (x : Rat) (n : Nat) : Rat :=
  sumPrefix (fun j => (-x)^j / (factorial j : Rat)) n

def exponential (xlo xhi : Rat) : Box := outward (taylor xhi 62) (taylor xlo 61)

def numeratorBox (l h : Int) : Box := ((l : Rat)/decimalScale, (h : Rat)/decimalScale)
def left : Rat := 70945978/10^8
def right : Rat := 70945980/10^8
def leftNome : Box := numeratorBox 107653920932681137362307339703 107653920932681137362307339704
def rightNome : Box := numeratorBox 107653914168586007217674787666 107653914168586007217674787667
def endpointNome : Box := numeratorBox 11936579997939637804831817728 11936581488001284678795808448
def nome (p : Box) (tlo thi : Rat) : Box := exponential (p.1*tlo) (p.2*thi)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem original_pi_box : piBox =
    numeratorBox 3141592653589793238462643383279 3141592653589793238462643383280 := by
  decide +kernel

theorem original_left_nome : nome piBox left left = leftNome := by
  rw [original_pi_box]
  decide +kernel

theorem original_right_nome : nome piBox right right = rightNome := by
  rw [original_pi_box]
  decide +kernel

theorem original_endpoint_nome : nome piBox (1/right) (1/left) = endpointNome := by
  rw [original_pi_box]
  decide +kernel

def normalizedF (t : Rat) : Box :=
  let q := nome piBox t t
  (1/4 - 2*(VerticalRunCore.seriesCut q.2 + VerticalRunCore.seriesTail q.2),
   1/4 - 2*VerticalRunCore.seriesCut q.1)

def printedLeft : Box :=
  (-47221253557264140850267997705597/10^40, -47221253557264140850240321370933/10^40)
def printedRight : Box :=
  (13998405173549555596490797567326/10^39, 13998405173549555596493565200718/10^39)
def printedT : Box :=
  (14095231329527057065107846843472/10^31, 14095231726878160732381474817360/10^31)

/-- Each displayed number is strictly within half a unit in its last place. -/
def roundedWithin (digits : Nat) (raw printed : Box) : Prop :=
  (raw.1 - printed.1).abs < 1/(2*10^digits) ∧
  (raw.2 - printed.2).abs < 1/(2*10^digits)

/-- The two original exact assertions, and the direction of rounding of
both entries in the first printed interval. -/
theorem left_log_arithmetic :
    let raw := normalizedF left;
    -48/10^10 < raw.1 ∧ raw.1 ≤ raw.2 ∧ raw.2 < -47/10^10 ∧
    printedLeft.1 < raw.1 ∧ printedLeft.2 < raw.2 ∧ roundedWithin 40 raw printedLeft := by
  dsimp only [normalizedF]
  rw [original_left_nome]
  unfold roundedWithin
  decide +kernel

theorem right_log_arithmetic :
    let raw := normalizedF right
    139/10^10 < raw.1 ∧ raw.1 ≤ raw.2 ∧ raw.2 < 140/10^10 ∧
    raw.1 < printedRight.1 ∧ printedRight.2 < raw.2 ∧ roundedWithin 39 raw printedRight := by
  dsimp only [normalizedF]
  rw [original_right_nome]
  unfold roundedWithin
  decide +kernel

theorem reciprocal_log_arithmetic :
    1/right < printedT.1 ∧ printedT.2 < 1/left ∧
    roundedWithin 31 (1/right, 1/left) printedT := by
  unfold roundedWithin
  decide +kernel

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.original_pi_box
#print axioms TwoAxisHelicoid.VerticalAttachment.original_left_nome
#print axioms TwoAxisHelicoid.VerticalAttachment.original_right_nome
#print axioms TwoAxisHelicoid.VerticalAttachment.original_endpoint_nome
#print axioms TwoAxisHelicoid.VerticalAttachment.left_log_arithmetic
#print axioms TwoAxisHelicoid.VerticalAttachment.right_log_arithmetic
#print axioms TwoAxisHelicoid.VerticalAttachment.reciprocal_log_arithmetic
