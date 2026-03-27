import FastMLFE2.Evaluation.ContinuousGrad
import FastMLFE2.Evaluation.StepEdgeFamilies

namespace FastMLFE2.Theorems

open FastMLFE2.Evaluation

theorem gaussian_pos (σ : GaussianScale) (x : ℝ) : 0 < gaussian σ x := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.2
    positivity
  have hden : 0 < σ.sigma * Real.sqrt (2 * Real.pi) := mul_pos σ.sigma_pos hsqrt
  exact mul_pos (one_div_pos.mpr hden) (Real.exp_pos _)

theorem gaussian_nonneg (σ : GaussianScale) (x : ℝ) : 0 ≤ gaussian σ x := by
  exact (gaussian_pos σ x).le

theorem gaussian_symm (σ : GaussianScale) (x : ℝ) :
    gaussian σ (-x) = gaussian σ x := by
  simp [gaussian]

theorem continuous_gaussian (σ : GaussianScale) : Continuous (gaussian σ) := by
  unfold gaussian
  fun_prop

theorem verticalEdgeGradMag_nonneg
    (σ : GaussianScale) (spec : VerticalEdgeSpec) (p : ℝ × ℝ) (c : Fin 3) :
    0 ≤ verticalEdgeGradMag σ spec p c := by
  exact mul_nonneg (abs_nonneg _) (gaussian_nonneg σ _)

theorem gradMetricContinuous_self
    (σ : GaussianScale) (window : RectWindow) (alpha : ContinuousGrayField)
    (spec : VerticalEdgeSpec) :
    gradMetricContinuous σ window alpha spec spec = 0 := by
  simp

theorem gradMetricContinuous_binaryEdge_self
    (σ : GaussianScale) (window : RectWindow) :
    gradMetricContinuous σ window windowAlphaOne
      (binaryBlackWhiteEdge 0) (binaryBlackWhiteEdge 0) = 0 := by
  simp

private theorem rgbL2Sq_nonneg_local (x : RGB) : 0 ≤ rgbL2Sq x := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem binaryFlatBlack_slice_eq
    (σ : GaussianScale) (window : RectWindow) (x : ℝ) :
    rgbL2Sq
      (rgbSub
        (verticalEdgeGradMag σ (binaryBlackWhiteEdge 0) (x, window.midY))
        (verticalEdgeGradMag σ (flatBlackEdge 0) (x, window.midY))) =
      3 * gaussian σ x ^ 2 := by
  simp [verticalEdgeGradMag, edgeContrast, rgbSub, rgbL2Sq, binaryBlackWhiteEdge,
    flatBlackEdge, flatEdge, blackRGB, whiteRGB]

private theorem shiftedBinary_slice_eq
    (σ : GaussianScale) (window : RectWindow) (x x0 x1 : ℝ) :
    rgbL2Sq
      (rgbSub
        (verticalEdgeGradMag σ (binaryBlackWhiteEdge x0) (x, window.midY))
        (verticalEdgeGradMag σ (binaryBlackWhiteEdge x1) (x, window.midY))) =
      3 * (gaussian σ (x - x0) - gaussian σ (x - x1)) ^ 2 := by
  simp [verticalEdgeGradMag, edgeContrast, rgbSub, rgbL2Sq, binaryBlackWhiteEdge,
    blackRGB, whiteRGB]

theorem edgeContrastL2Sq_binaryBlackWhiteEdge
    (x0 : ℝ) :
    edgeContrastL2Sq (binaryBlackWhiteEdge x0) = 3 := by
  simp [edgeContrastL2Sq, edgeContrast, rgbL2Sq, rgbSub, binaryBlackWhiteEdge, blackRGB, whiteRGB]

theorem edgeContrastL2Sq_flatBlackEdge
    (x0 : ℝ) :
    edgeContrastL2Sq (flatBlackEdge x0) = 0 := by
  simp [edgeContrastL2Sq, edgeContrast, rgbL2Sq, rgbSub, flatBlackEdge, flatEdge, blackRGB]

theorem gradMetricContinuous_nonneg_windowAlphaOne
    (σ : GaussianScale) (window : RectWindow) (estimated reference : VerticalEdgeSpec) :
    0 ≤ gradMetricContinuous σ window windowAlphaOne estimated reference := by
  unfold gradMetricContinuous
  have hInt :
      0 ≤
        ∫ x in window.xMin..window.xMax,
          windowAlphaOne (x, window.midY) *
            rgbL2Sq
              (rgbSub
                (verticalEdgeGradMag σ estimated (x, window.midY))
                (verticalEdgeGradMag σ reference (x, window.midY))) := by
    apply intervalIntegral.integral_nonneg window.x_lt.le
    intro x hx
    simpa only [windowAlphaOne_apply, one_mul] using rgbL2Sq_nonneg_local _
  exact mul_nonneg window.height_pos.le hInt

theorem gradMetricContinuous_binaryEdge_vs_flatBlack_ge_of_lowerBound
    (σ : GaussianScale) (window : RectWindow) {μ : ℝ}
    (hμ0 : 0 ≤ μ)
    (hμ : ∀ x ∈ Set.Icc window.xMin window.xMax, μ ≤ gaussian σ x) :
    window.height * window.width * (3 * μ ^ 2) ≤
      gradMetricContinuous σ window windowAlphaOne (binaryBlackWhiteEdge 0) (flatBlackEdge 0) := by
  unfold gradMetricContinuous RectWindow.width
  have hcont :
      Continuous fun x : ℝ => 3 * gaussian σ x ^ 2 := by
    simpa using continuous_const.mul ((continuous_gaussian σ).pow 2)
  have hint :
      IntervalIntegrable (fun x : ℝ => 3 * gaussian σ x ^ 2) MeasureTheory.volume
        window.xMin window.xMax :=
    hcont.intervalIntegrable _ _
  have hconstInt :
      IntervalIntegrable
        (fun _x : ℝ => 3 * μ ^ 2)
        MeasureTheory.volume window.xMin window.xMax := by
    simp
  have hmono :
      ∀ x ∈ Set.Icc window.xMin window.xMax, 3 * μ ^ 2 ≤ 3 * gaussian σ x ^ 2 := by
    intro x hx
    have hg : μ ^ 2 ≤ gaussian σ x ^ 2 := by
      have hle := hμ x hx
      nlinarith [hμ0, gaussian_nonneg σ x]
    nlinarith
  have hIntLower :=
    intervalIntegral.integral_mono_on window.x_lt.le hconstInt hint hmono
  have hconst :
      ∫ x in window.xMin..window.xMax, (3 * μ ^ 2 : ℝ) =
        (window.xMax - window.xMin) * (3 * μ ^ 2) := by
    simp [intervalIntegral.integral_const]
    ring
  calc
    window.height * (window.xMax - window.xMin) * (3 * μ ^ 2)
        = window.height * (∫ x in window.xMin..window.xMax, (3 * μ ^ 2 : ℝ)) := by
            rw [hconst]
            ring_nf
    _ ≤ window.height *
          (∫ x in window.xMin..window.xMax, 3 * gaussian σ x ^ 2) := by
            exact mul_le_mul_of_nonneg_left hIntLower window.height_pos.le
    _ = gradMetricContinuous σ window windowAlphaOne
          (binaryBlackWhiteEdge 0) (flatBlackEdge 0) := by
            simp [gradMetricContinuous, windowAlphaOne, binaryFlatBlack_slice_eq]

theorem gradMetricContinuous_shiftedBinaryEdges_ge_of_lowerBound
    (σ : GaussianScale) (window : RectWindow) {x0 x1 μ : ℝ}
    (hμ0 : 0 ≤ μ)
    (hμ : ∀ x ∈ Set.Icc window.xMin window.xMax,
      μ ≤ |gaussian σ (x - x0) - gaussian σ (x - x1)|) :
    window.height * window.width * (3 * μ ^ 2) ≤
      gradMetricContinuous σ window windowAlphaOne
        (binaryBlackWhiteEdge x0) (binaryBlackWhiteEdge x1) := by
  unfold gradMetricContinuous RectWindow.width
  have hshift0 : Continuous fun x : ℝ => gaussian σ (x - x0) := by
    simpa using (continuous_gaussian σ).comp (continuous_id.sub continuous_const)
  have hshift1 : Continuous fun x : ℝ => gaussian σ (x - x1) := by
    simpa using (continuous_gaussian σ).comp (continuous_id.sub continuous_const)
  have hdiff : Continuous fun x : ℝ => gaussian σ (x - x0) - gaussian σ (x - x1) := by
    exact hshift0.sub hshift1
  have hcont :
      Continuous fun x : ℝ => 3 * (gaussian σ (x - x0) - gaussian σ (x - x1)) ^ 2 := by
    simpa using continuous_const.mul (hdiff.pow 2)
  have hint :
      IntervalIntegrable
        (fun x : ℝ => 3 * (gaussian σ (x - x0) - gaussian σ (x - x1)) ^ 2)
        MeasureTheory.volume window.xMin window.xMax :=
    hcont.intervalIntegrable _ _
  have hconstInt :
      IntervalIntegrable
        (fun _x : ℝ => 3 * μ ^ 2)
        MeasureTheory.volume window.xMin window.xMax := by
    simp
  have hmono :
      ∀ x ∈ Set.Icc window.xMin window.xMax,
        3 * μ ^ 2 ≤ 3 * (gaussian σ (x - x0) - gaussian σ (x - x1)) ^ 2 := by
    intro x hx
    have hg : μ ^ 2 ≤ |gaussian σ (x - x0) - gaussian σ (x - x1)| ^ 2 := by
      have hle := hμ x hx
      nlinarith [hμ0, abs_nonneg (gaussian σ (x - x0) - gaussian σ (x - x1))]
    have habs : |gaussian σ (x - x0) - gaussian σ (x - x1)| ^ 2 =
        (gaussian σ (x - x0) - gaussian σ (x - x1)) ^ 2 := by
      rw [sq_abs]
    rw [habs] at hg
    nlinarith
  have hIntLower :=
    intervalIntegral.integral_mono_on window.x_lt.le hconstInt hint hmono
  have hconst :
      ∫ x in window.xMin..window.xMax, (3 * μ ^ 2 : ℝ) =
        (window.xMax - window.xMin) * (3 * μ ^ 2) := by
    simp [intervalIntegral.integral_const]
    ring
  calc
    window.height * (window.xMax - window.xMin) * (3 * μ ^ 2)
        = window.height * (∫ x in window.xMin..window.xMax, (3 * μ ^ 2 : ℝ)) := by
            rw [hconst]
            ring_nf
    _ ≤ window.height *
          (∫ x in window.xMin..window.xMax,
            3 * (gaussian σ (x - x0) - gaussian σ (x - x1)) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hIntLower window.height_pos.le
    _ = gradMetricContinuous σ window windowAlphaOne
          (binaryBlackWhiteEdge x0) (binaryBlackWhiteEdge x1) := by
            simp [gradMetricContinuous, windowAlphaOne, shiftedBinary_slice_eq]

end FastMLFE2.Theorems
