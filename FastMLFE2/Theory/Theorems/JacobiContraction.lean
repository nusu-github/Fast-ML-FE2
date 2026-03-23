import FastMLFE2.Theory.Theorems.Conditioning
import FastMLFE2.Theory.Theorems.BinaryAlpha

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

def jacobiDiagForeground (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter ^ 2 + ctx.totalWeight

def jacobiDiagBackground (ctx : LocalContext ι) : ℝ :=
  (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight

def jacobiCrossTerm (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter * (1 - ctx.alphaCenter)

noncomputable def jacobiForegroundCoeff (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / jacobiDiagForeground ctx

noncomputable def jacobiBackgroundCoeff (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / jacobiDiagBackground ctx

noncomputable def jacobiStep (ctx : LocalContext ι) (g : LocalUnknown) : LocalUnknown :=
  mkLocalUnknown
    ((foreground ctx.rhs - jacobiCrossTerm ctx * background g) / jacobiDiagForeground ctx)
    ((background ctx.rhs - jacobiCrossTerm ctx * foreground g) / jacobiDiagBackground ctx)

noncomputable def jacobiDifferenceMap (ctx : LocalContext ι) (g : LocalUnknown) : LocalUnknown :=
  mkLocalUnknown
    (-(jacobiForegroundCoeff ctx) * background g)
    (-(jacobiBackgroundCoeff ctx) * foreground g)

def localInfinityNorm (g : LocalUnknown) : ℝ :=
  max |foreground g| |background g|

noncomputable def jacobiSpectralRadiusSq (ctx : LocalContext ι) : ℝ :=
  jacobiForegroundCoeff ctx * jacobiBackgroundCoeff ctx

noncomputable def jacobiSpectralRadius (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / Real.sqrt (jacobiDiagForeground ctx * jacobiDiagBackground ctx)

@[simp] theorem jacobiStep_foreground
    (ctx : LocalContext ι) (g : LocalUnknown) :
    foreground (jacobiStep ctx g) =
      (foreground ctx.rhs - jacobiCrossTerm ctx * background g) / jacobiDiagForeground ctx := by
  simp [jacobiStep]

@[simp] theorem jacobiStep_background
    (ctx : LocalContext ι) (g : LocalUnknown) :
    background (jacobiStep ctx g) =
      (background ctx.rhs - jacobiCrossTerm ctx * foreground g) / jacobiDiagBackground ctx := by
  simp [jacobiStep]

@[simp] theorem jacobiDifferenceMap_foreground
    (ctx : LocalContext ι) (g : LocalUnknown) :
    foreground (jacobiDifferenceMap ctx g) =
      -(jacobiForegroundCoeff ctx) * background g := by
  simp [jacobiDifferenceMap]

@[simp] theorem jacobiDifferenceMap_background
    (ctx : LocalContext ι) (g : LocalUnknown) :
    background (jacobiDifferenceMap ctx g) =
      -(jacobiBackgroundCoeff ctx) * foreground g := by
  simp [jacobiDifferenceMap]

theorem jacobiStep_sub_eq
    (ctx : LocalContext ι) (x y : LocalUnknown) :
    jacobiStep ctx x - jacobiStep ctx y = jacobiDifferenceMap ctx (x - y) := by
  ext i
  fin_cases i
  · simp [sub_eq_add_neg, jacobiStep, jacobiDifferenceMap, jacobiForegroundCoeff, jacobiCrossTerm,
      jacobiDiagForeground, foreground, background, mkLocalUnknown]
    ring_nf
  · simp [sub_eq_add_neg, jacobiStep, jacobiDifferenceMap, jacobiBackgroundCoeff, jacobiCrossTerm,
      jacobiDiagBackground, foreground, background, mkLocalUnknown]
    ring_nf

theorem jacobiDifferenceMap_sq_eq
    (ctx : LocalContext ι) (g : LocalUnknown) :
    jacobiDifferenceMap ctx (jacobiDifferenceMap ctx g) =
      fun i => jacobiSpectralRadiusSq ctx * g i := by
  ext i
  fin_cases i
  · simp [jacobiDifferenceMap, jacobiSpectralRadiusSq, jacobiForegroundCoeff, jacobiBackgroundCoeff,
      foreground, background, mkLocalUnknown]
    ring_nf
  · simp [jacobiDifferenceMap, jacobiSpectralRadiusSq, jacobiForegroundCoeff, jacobiBackgroundCoeff,
      foreground, background, mkLocalUnknown]
    ring_nf

theorem jacobiDiagForeground_pos
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < jacobiDiagForeground ctx := by
  simpa [jacobiDiagForeground] using
    add_pos_of_nonneg_of_pos (sq_nonneg ctx.alphaCenter) (totalWeight_pos ctx)

theorem jacobiDiagBackground_pos
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < jacobiDiagBackground ctx := by
  simpa [jacobiDiagBackground, add_comm] using
    add_pos_of_nonneg_of_pos (sq_nonneg (1 - ctx.alphaCenter)) (totalWeight_pos ctx)

theorem jacobiCrossTerm_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ jacobiCrossTerm ctx := by
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  simpa [jacobiCrossTerm] using mul_nonneg hα.1 (sub_nonneg.2 hα.2)

theorem jacobiSpectralRadiusSq_eq
    (ctx : LocalContext ι) :
    jacobiSpectralRadiusSq ctx =
      (ctx.alphaCenter * (1 - ctx.alphaCenter)) ^ 2 /
        ((ctx.alphaCenter ^ 2 + ctx.totalWeight) *
          ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight)) := by
  simp [jacobiSpectralRadiusSq, jacobiForegroundCoeff, jacobiBackgroundCoeff,
    jacobiCrossTerm, jacobiDiagForeground, jacobiDiagBackground]
  ring_nf
  field_simp
  ring

private theorem sq_div_sqrt
    {a b : ℝ}
    (hb : 0 < b) :
    (a / Real.sqrt b) ^ 2 = a ^ 2 / b := by
  have hsqrt_ne : Real.sqrt b ≠ 0 := by
    exact (Real.sqrt_ne_zero hb.le).2 hb.ne'
  field_simp [pow_two, hsqrt_ne]
  rw [Real.sq_sqrt hb.le]

theorem jacobiSpectralRadius_sq
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    jacobiSpectralRadius ctx ^ 2 = jacobiSpectralRadiusSq ctx := by
  have hprod : 0 < jacobiDiagForeground ctx * jacobiDiagBackground ctx := by
    exact mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx)
  rw [jacobiSpectralRadius, jacobiSpectralRadiusSq_eq]
  rw [sq_div_sqrt hprod]
  simp [jacobiCrossTerm, jacobiDiagForeground, jacobiDiagBackground]

theorem jacobiSpectralRadius_lt_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    jacobiSpectralRadius ctx < 1 := by
  have hsq_lt :
      jacobiSpectralRadius ctx ^ 2 < 1 := by
    rw [jacobiSpectralRadius_sq, jacobiSpectralRadiusSq_eq]
    have hden :
        0 < (ctx.alphaCenter ^ 2 + ctx.totalWeight) *
          ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) := by
      exact mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx)
    have hnum :
        (ctx.alphaCenter * (1 - ctx.alphaCenter)) ^ 2 <
          (ctx.alphaCenter ^ 2 + ctx.totalWeight) *
            ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) := by
      have htw : 0 < ctx.totalWeight := totalWeight_pos ctx
      nlinarith
    have hnonneg : 0 ≤ (ctx.alphaCenter * (1 - ctx.alphaCenter)) ^ 2 := sq_nonneg _
    exact (div_lt_one hden).2 hnum
  have hnonneg : 0 ≤ jacobiSpectralRadius ctx := by
    have hcross : 0 ≤ jacobiCrossTerm ctx := jacobiCrossTerm_nonneg ctx
    exact div_nonneg hcross (Real.sqrt_nonneg _)
  nlinarith

theorem jacobiSpectralRadius_eq_zero_of_alpha_zero
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 0) :
    jacobiSpectralRadius ctx = 0 := by
  simp [jacobiSpectralRadius, jacobiCrossTerm, hα]

theorem jacobiSpectralRadius_eq_zero_of_alpha_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 1) :
    jacobiSpectralRadius ctx = 0 := by
  simp [jacobiSpectralRadius, jacobiCrossTerm, hα]

theorem jacobiTwoStep_sub_eq
    (ctx : LocalContext ι) (x y : LocalUnknown) :
    jacobiStep ctx (jacobiStep ctx x) - jacobiStep ctx (jacobiStep ctx y) =
      fun i => jacobiSpectralRadiusSq ctx * (x - y) i := by
  rw [jacobiStep_sub_eq, jacobiStep_sub_eq]
  exact jacobiDifferenceMap_sq_eq ctx (x - y)

theorem localInfinityNorm_smul_nonneg
    {c : ℝ} (hc : 0 ≤ c) (g : LocalUnknown) :
    localInfinityNorm (fun i => c * g i) = c * localInfinityNorm g := by
  simp [localInfinityNorm, foreground, background, abs_mul, abs_of_nonneg hc,
    mul_max_of_nonneg, hc]

theorem jacobiTwoStep_infty_contraction
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (x y : LocalUnknown) :
    localInfinityNorm (jacobiStep ctx (jacobiStep ctx x) - jacobiStep ctx (jacobiStep ctx y)) =
      jacobiSpectralRadiusSq ctx * localInfinityNorm (x - y) := by
  rw [jacobiTwoStep_sub_eq]
  have hsq_nonneg : 0 ≤ jacobiSpectralRadiusSq ctx := by
    rw [jacobiSpectralRadiusSq_eq]
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx)))
  exact localInfinityNorm_smul_nonneg hsq_nonneg (x - y)

example (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 0) :
    jacobiSpectralRadius ctx = 0 := by
  simpa using jacobiSpectralRadius_eq_zero_of_alpha_zero (ctx := ctx) hα

example (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 1) :
    jacobiSpectralRadius ctx = 0 := by
  simpa using jacobiSpectralRadius_eq_zero_of_alpha_one (ctx := ctx) hα

end LocalContext

end FastMLFE2.Theory.Theorems
