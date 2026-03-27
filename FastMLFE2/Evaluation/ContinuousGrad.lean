import FastMLFE2.Evaluation.ForegroundMetrics
import Mathlib

namespace FastMLFE2.Evaluation

abbrev ContinuousGrayField := ℝ × ℝ → ℝ

abbrev ContinuousRGBImage := ℝ × ℝ → RGB

structure GaussianScale where
  sigma : ℝ
  sigma_pos : 0 < sigma

structure RectWindow where
  xMin : ℝ
  xMax : ℝ
  yMin : ℝ
  yMax : ℝ
  x_lt : xMin < xMax
  y_lt : yMin < yMax

namespace RectWindow

def width (window : RectWindow) : ℝ :=
  window.xMax - window.xMin

def height (window : RectWindow) : ℝ :=
  window.yMax - window.yMin

noncomputable def midY (window : RectWindow) : ℝ :=
  (window.yMin + window.yMax) / 2

@[simp] theorem width_pos (window : RectWindow) : 0 < window.width := by
  simp [width, sub_pos, window.x_lt]

@[simp] theorem height_pos (window : RectWindow) : 0 < window.height := by
  simp [height, sub_pos, window.y_lt]

end RectWindow

/-- Normalized one-dimensional Gaussian with scale `σ`. -/
noncomputable def gaussian (σ : GaussianScale) (x : ℝ) : ℝ :=
  (1 / (σ.sigma * Real.sqrt (2 * Real.pi))) * Real.exp (-(x ^ 2) / (2 * σ.sigma ^ 2))

/-- Derivative of the normalized one-dimensional Gaussian. -/
noncomputable def gaussianDeriv (σ : GaussianScale) (x : ℝ) : ℝ :=
  -(x / (σ.sigma ^ 2)) * gaussian σ x

structure VerticalEdgeSpec where
  x0 : ℝ
  leftColor : RGB
  rightColor : RGB

/-- Constant continuous RGB image. -/
def constantRGB (color : RGB) : ContinuousRGBImage :=
  fun _ => color

/-- RGB-valued vertical step edge at `x = x0`. -/
noncomputable def verticalStepRGB (spec : VerticalEdgeSpec) : ContinuousRGBImage :=
  fun p c => if p.1 < spec.x0 then spec.leftColor c else spec.rightColor c

/-- Channelwise edge contrast `right - left`. -/
def edgeContrast (spec : VerticalEdgeSpec) : RGB :=
  rgbSub spec.rightColor spec.leftColor

/-- Squared RGB contrast energy. -/
def edgeContrastL2Sq (spec : VerticalEdgeSpec) : ℝ :=
  rgbL2Sq (edgeContrast spec)

/-- Specialized continuous gradient magnitude for a vertical step edge under Gaussian smoothing. -/
noncomputable def verticalEdgeGradMag (σ : GaussianScale) (spec : VerticalEdgeSpec) :
    ContinuousRGBImage :=
  fun p c => |edgeContrast spec c| * gaussian σ (p.1 - spec.x0)

/-- Continuous GRAD on a finite window, specialized to vertical-edge gradient magnitudes. -/
noncomputable def gradMetricContinuous (σ : GaussianScale) (window : RectWindow)
    (alpha : ContinuousGrayField) (estimated reference : VerticalEdgeSpec) : ℝ :=
  window.height *
    ∫ x in window.xMin..window.xMax,
      alpha (x, window.midY) *
        rgbL2Sq
          (rgbSub
            (verticalEdgeGradMag σ estimated (x, window.midY))
            (verticalEdgeGradMag σ reference (x, window.midY)))

@[simp] theorem constantRGB_apply (color : RGB) (p : ℝ × ℝ) :
    constantRGB color p = color := rfl

@[simp] theorem verticalStepRGB_left
    (spec : VerticalEdgeSpec) (p : ℝ × ℝ) (c : Fin 3) (hp : p.1 < spec.x0) :
    verticalStepRGB spec p c = spec.leftColor c := by
  simp [verticalStepRGB, hp]

@[simp] theorem verticalStepRGB_right
    (spec : VerticalEdgeSpec) (p : ℝ × ℝ) (c : Fin 3) (hp : ¬ p.1 < spec.x0) :
    verticalStepRGB spec p c = spec.rightColor c := by
  simp [verticalStepRGB, hp]

@[simp] theorem edgeContrast_apply (spec : VerticalEdgeSpec) (c : Fin 3) :
    edgeContrast spec c = spec.rightColor c - spec.leftColor c := by
  simp [edgeContrast, rgbSub]

@[simp] theorem verticalEdgeGradMag_apply
    (σ : GaussianScale) (spec : VerticalEdgeSpec) (p : ℝ × ℝ) (c : Fin 3) :
    verticalEdgeGradMag σ spec p c =
      |edgeContrast spec c| * gaussian σ (p.1 - spec.x0) := rfl

@[simp] theorem gradMetricContinuous_eq_zero_of_eq
    (σ : GaussianScale) (window : RectWindow) (alpha : ContinuousGrayField)
    (spec : VerticalEdgeSpec) :
    gradMetricContinuous σ window alpha spec spec = 0 := by
  simp [gradMetricContinuous]

end FastMLFE2.Evaluation
