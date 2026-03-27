import FastMLFE2.Evaluation.DiscreteGrad

namespace FastMLFE2.Evaluation

open FastMLFE2.Canonical

def blackRGBDiscrete : RGB :=
  fun _ => 0

def whiteRGBDiscrete : RGB :=
  fun _ => 1

def unitWeights {h w : Nat} : GrayField h w :=
  fun _ => 1

def singletonMask {h w : Nat} (p : Pixel h w) : PixelMask h w :=
  {p}

def flatBlackImage {h w : Nat} : RGBImage h w :=
  fun _ _ => 0

def verticalStepImage {h w : Nat} (x0 : Nat) : RGBImage h w :=
  fun p _ => if p.2.1 < x0 then 0 else 1

def centeredVerticalStepImage {h w : Nat} : RGBImage h w :=
  verticalStepImage 8

def shiftedVerticalStepImage {h w : Nat} : RGBImage h w :=
  verticalStepImage 9

def saturatingStepAlpha {h w : Nat} : GrayField h w :=
  fun _ => 1

def witnessPixel {h w : Nat} [Fact (8 < h)] [Fact (7 < w)] : Pixel h w :=
  (⟨8, Fact.out⟩, ⟨7, Fact.out⟩)

@[simp] theorem verticalStepImage_apply_left
    {h w : Nat} (x0 : Nat) (p : Pixel h w) (c : Fin 3)
    (hp : p.2.1 < x0) :
    verticalStepImage x0 p c = 0 := by
  simp [verticalStepImage, hp]

@[simp] theorem verticalStepImage_apply_right
    {h w : Nat} (x0 : Nat) (p : Pixel h w) (c : Fin 3)
    (hp : ¬ p.2.1 < x0) :
    verticalStepImage x0 p c = 1 := by
  simp [verticalStepImage, hp]

end FastMLFE2.Evaluation
