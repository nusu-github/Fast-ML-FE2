import FastMLFE2.Theorems.Grid.CanonicalMultilevelConvergence
import FastMLFE2.Theorems.Grid.GridAssumptions
import FastMLFE2.Theorems.Grid.GridNonempty
import FastMLFE2.Theorems.Grid.IterationInvariance
import FastMLFE2.Theorems.Grid.ChannelReuse

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Level
open FastMLFE2.Canonical
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

noncomputable def closedFormForegroundLipschitzFactor (ctx : LocalContext ι) : ℝ :=
  (jacobiDiagBackground ctx + jacobiCrossTerm ctx) / closedFormDenom ctx

noncomputable def closedFormBackgroundLipschitzFactor (ctx : LocalContext ι) : ℝ :=
  (jacobiDiagForeground ctx + jacobiCrossTerm ctx) / closedFormDenom ctx

noncomputable def closedFormOneStepGain (ctx : LocalContext ι) : ℝ :=
  ctx.totalWeight *
    max (closedFormForegroundLipschitzFactor ctx) (closedFormBackgroundLipschitzFactor ctx)

theorem closedFormForegroundLipschitzFactor_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ closedFormForegroundLipschitzFactor ctx := by
  unfold closedFormForegroundLipschitzFactor
  exact div_nonneg
    (add_nonneg (jacobiDiagBackground_pos ctx).le (jacobiCrossTerm_nonneg ctx))
    (closedFormDenom_pos ctx).le

theorem closedFormBackgroundLipschitzFactor_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ closedFormBackgroundLipschitzFactor ctx := by
  unfold closedFormBackgroundLipschitzFactor
  exact div_nonneg
    (add_nonneg (jacobiDiagForeground_pos ctx).le (jacobiCrossTerm_nonneg ctx))
    (closedFormDenom_pos ctx).le

theorem closedFormOneStepGain_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ closedFormOneStepGain ctx := by
  unfold closedFormOneStepGain
  exact mul_nonneg (le_of_lt (totalWeight_pos ctx))
    (le_trans
      (closedFormForegroundLipschitzFactor_nonneg ctx)
      (le_max_left _ _))

end LocalContext

end FastMLFE2.Theorems
