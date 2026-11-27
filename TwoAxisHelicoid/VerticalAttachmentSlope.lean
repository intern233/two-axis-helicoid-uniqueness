module

public import TwoAxisHelicoid.VerticalAttachmentArithmetic

@[expose] public section
namespace TwoAxisHelicoid.VerticalAttachment

def boxAdd (x y : Box) : Box := outward (x.1+y.1) (x.2+y.2)
def boxNeg (x : Box) : Box := (-x.2, -x.1)
def boxMul (x y : Box) : Box :=
  let a := x.1*y.1
  let b := x.1*y.2
  let c := x.2*y.1
  let d := x.2*y.2
  outward (min (min a b) (min c d)) (max (max a b) (max c d))
def boxDiv (x y : Box) : Box := boxMul x (1/y.2, 1/y.1)
def boxScale (x : Box) (k : Rat) : Box := boxMul x (k,k)
def oneBox : Box := (1,1)

def signedPower (q : Box) (n : Nat) : Box :=
  let v := (q.1^n, q.2^n)
  if n % 2 = 1 then boxNeg v else v

def lambertPrefix (q : Box) (power : Nat) : Nat → Box
  | 0 => (0,0)
  | n+1 =>
    let r := signedPower q (n+1)
    let v := boxDiv r (boxAdd oneBox (boxNeg r))
    boxAdd (lambertPrefix q power n) (boxScale v ((n+1 : Nat)^power : Nat))

def lambertBox (q : Box) (power : Nat) : Box :=
  let x := q.2
  let m : Rat := 21
  let d := 1-x
  let tail := x^21 * (if power = 1 then m/d+x/d^2 else
    m^3/d+3*m^2*x/d^2+3*m*x*(1+x)/d^3+x*(1+4*x+x*x)/d^4) / d
  boxAdd (lambertPrefix q power 20) (-tail,tail)

def endS1 : Box := numeratorBox (-11515797946380198074838040054) (-11515796383408557180681251092)
def endS3 : Box := numeratorBox (-10700412763187882203048570054) (-10700410970807588360172963406)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem original_lambert_divisors_positive : ∀ i : Fin 20,
    let d := boxAdd oneBox (boxNeg (signedPower endpointNome (i.val+1)))
    0 < d.1 ∧ 0 < d.2 := by decide +kernel

theorem original_lambert_one : lambertBox endpointNome 1 = endS1 := by decide +kernel
theorem original_lambert_three : lambertBox endpointNome 3 = endS3 := by decide +kernel

def slopeBox : Box :=
  let t : Box := (1/right,1/left)
  let q := nome piBox t.1 t.2
  let s1 := lambertBox q 1
  let s3 := lambertBox q 3
  let pi2 := boxMul piBox piBox
  let pi4 := boxMul pi2 pi2
  let eta := boxScale (boxMul pi2 (boxAdd oneBox (boxScale s1 (-24)))) (1/12)
  let g2 := boxScale (boxMul pi4 (boxAdd oneBox (boxScale s3 240))) (1/12)
  let f := boxDiv piBox t
  let e := boxAdd f (boxNeg eta)
  let c := boxAdd (boxScale (boxMul e e) 6) (boxScale g2 (-1/2))
  let num := boxAdd (boxMul f f) (boxScale (boxMul e f) 2)
  boxDiv (boxAdd num (boxScale c (-2/3))) piBox

/-- Both slope bounds in the original attachment are exactly on its decimal
grid and both lie inside the asserted interval (0.13,0.14). -/
theorem original_slope_log_arithmetic :
    slopeBox = numeratorBox 133652317282437548238921248808 133653238307059875782433586357 ∧
    13/100 < slopeBox.1 ∧ slopeBox.1 ≤ slopeBox.2 ∧ slopeBox.2 < 14/100 := by
  have value : slopeBox = numeratorBox 133652317282437548238921248808
      133653238307059875782433586357 := by
    unfold slopeBox
    dsimp only
    rw [original_endpoint_nome, original_lambert_one, original_lambert_three, original_pi_box]
    decide +kernel
  rw [value]
  decide +kernel

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.original_lambert_divisors_positive
#print axioms TwoAxisHelicoid.VerticalAttachment.original_lambert_one
#print axioms TwoAxisHelicoid.VerticalAttachment.original_lambert_three
#print axioms TwoAxisHelicoid.VerticalAttachment.original_slope_log_arithmetic
