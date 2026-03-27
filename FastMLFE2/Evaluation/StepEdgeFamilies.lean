import FastMLFE2.Evaluation.ContinuousGrad

namespace FastMLFE2.Evaluation

def blackRGB : RGB :=
  fun _ => 0

def whiteRGB : RGB :=
  fun _ => 1

def windowAlphaOne : ContinuousGrayField :=
  fun _ => 1

def flatEdge (x0 : ℝ) (color : RGB) : VerticalEdgeSpec where
  x0 := x0
  leftColor := color
  rightColor := color

def flatBlackEdge (x0 : ℝ) : VerticalEdgeSpec :=
  flatEdge x0 blackRGB

def binaryBlackWhiteEdge (x0 : ℝ) : VerticalEdgeSpec where
  x0 := x0
  leftColor := blackRGB
  rightColor := whiteRGB

def shiftedBinaryBlackWhiteEdges (x0 x1 : ℝ) : VerticalEdgeSpec × VerticalEdgeSpec :=
  (binaryBlackWhiteEdge x0, binaryBlackWhiteEdge x1)

@[simp] theorem blackRGB_apply (c : Fin 3) : blackRGB c = 0 := rfl

@[simp] theorem whiteRGB_apply (c : Fin 3) : whiteRGB c = 1 := rfl

@[simp] theorem windowAlphaOne_apply (p : ℝ × ℝ) : windowAlphaOne p = 1 := rfl

@[simp] theorem flatEdge_leftColor (x0 : ℝ) (color : RGB) :
    (flatEdge x0 color).leftColor = color := rfl

@[simp] theorem flatEdge_rightColor (x0 : ℝ) (color : RGB) :
    (flatEdge x0 color).rightColor = color := rfl

@[simp] theorem binaryBlackWhiteEdge_left_apply (x0 : ℝ) (c : Fin 3) :
    (binaryBlackWhiteEdge x0).leftColor c = 0 := rfl

@[simp] theorem binaryBlackWhiteEdge_right_apply (x0 : ℝ) (c : Fin 3) :
    (binaryBlackWhiteEdge x0).rightColor c = 1 := rfl

end FastMLFE2.Evaluation
