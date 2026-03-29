import FastMLFE2.Theorems.Grid.MultilevelProxySimulation
import FastMLFE2.Theorems.Grid.CanonicalStepStability
import FastMLFE2.Theorems.Grid.CanonicalTransferGap

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Level
open FastMLFE2.Canonical

namespace Canonical

noncomputable def canonicalProxyLevelRun
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    (τ : ℝ)
    (state : GridState spec.height spec.width) : GridState spec.height spec.width :=
  Nat.iterate (nearBinaryProxyStep data spec τ) spec.iterations state

noncomputable def canonicalProxyMultilevelStep
    (data : (h w : Nat) → GridPixelData h w)
    (τ : ℝ)
    (target : RealLevelSpec)
    (state : SomeGridState) : SomeGridState :=
  ⟨target, canonicalProxyLevelRun data target τ (resizeSomeGridState target state)⟩

noncomputable def canonicalProxyMultilevelRun
    (data : (h w : Nat) → GridPixelData h w)
    (τ : ℝ)
    (seed : SomeGridState)
    (levels : List RealLevelSpec) : SomeGridState :=
  levels.foldl (fun state target => canonicalProxyMultilevelStep data τ target state) seed

section Simulation

variable
  (data : (h w : Nat) → GridPixelData h w)
  (gain : RealLevelSpec → ℝ)
  (τ : ℝ)
  (hgain_nonneg : ∀ (spec : RealLevelSpec), 0 ≤ gain spec)
  (hτ : 0 ≤ τ)
  (hheight : ∀ (spec : RealLevelSpec), 2 ≤ spec.height)
  (hwidth : ∀ (spec : RealLevelSpec), 2 ≤ spec.width)
  (hgrid : ∀ (spec : RealLevelSpec), GridMathAssumptions (data spec.height spec.width))
  (hgain :
    ∀ (spec : RealLevelSpec) (x y : GridState spec.height spec.width),
      gridStateDistance spec
          ((data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep x)
          ((data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep y) ≤
        gain spec * gridStateDistance spec x y)
  (himage :
    ∀ (spec : RealLevelSpec) (p : Pixel spec.height spec.width),
      0 ≤ (data spec.height spec.width).image p ∧
        (data spec.height spec.width).image p ≤ 1)
  (hnear :
    ∀ (spec : RealLevelSpec) (p : Pixel spec.height spec.width),
      (data spec.height spec.width).alpha p ≤ τ ∨
        1 - (data spec.height spec.width).alpha p ≤ τ)

include data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear

noncomputable def canonicalOneStepW :
    ProxySimulationWitness (fun spec => GridState spec.height spec.width) where
  resize := fun {src dst} state => resizeSomeGridState dst ⟨src, state⟩
  run := fun spec =>
    (data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep
  proxyRun := fun spec => nearBinaryProxyStep data spec τ
  dist := gridStateDistance
  gain := gain
  runGap := fun _ => 4 * τ
  dist_nonneg := gridStateDistance_nonneg
  dist_triangle := gridStateDistance_triangle
  gain_nonneg := hgain_nonneg
  runGap_nonneg := fun _ => by nlinarith
  resize_dist_le := fun src dst x y => gridStateDistance_resizeSomeGridState_le src dst x y
  run_lipschitz := hgain
  run_proxy_gap := by
    intro spec state
    letI : Fact (2 ≤ spec.height) := ⟨hheight spec⟩
    letI : Fact (2 ≤ spec.width) := ⟨hwidth spec⟩
    letI : GridMathAssumptions (data spec.height spec.width) := hgrid spec
    exact canonical_jacobiStep_proxy_gap_le_unconditional
      data spec τ hτ state (himage spec) (hnear spec)

noncomputable abbrev canonicalOneStepRunSeries (spec : RealLevelSpec) : ℝ :=
  ProxySimulationWitness.iterateRunSeries (canonicalOneStepW data gain τ hgain_nonneg hτ
    hheight hwidth hgrid hgain himage hnear) spec spec.iterations

theorem canonicalLevelRun_lipschitz
    (spec : RealLevelSpec)
    (x y : GridState spec.height spec.width) :
    gridStateDistance spec (canonicalLevelRun data spec x) (canonicalLevelRun data spec y) ≤
      gain spec ^ spec.iterations * gridStateDistance spec x y := by
  simpa [canonicalLevelRun, canonicalOneStepW]
    using ProxySimulationWitness.run_iterate_lipschitz
      (canonicalOneStepW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      spec spec.iterations x y

theorem canonicalLevelRun_exact_vs_proxy_le
    (spec : RealLevelSpec)
    (x y : GridState spec.height spec.width) :
    gridStateDistance spec
        (canonicalLevelRun data spec x)
        (canonicalProxyLevelRun data spec τ y) ≤
      gain spec ^ spec.iterations * gridStateDistance spec x y +
        canonicalOneStepRunSeries
          data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear spec := by
  simpa [canonicalLevelRun, canonicalProxyLevelRun, canonicalOneStepW,
      canonicalOneStepRunSeries]
    using ProxySimulationWitness.exact_vs_proxy_iterate_le
      (canonicalOneStepW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      spec spec.iterations x y

theorem canonicalLevelRun_exact_vs_proxy_le_same_seed
    (spec : RealLevelSpec)
    (state : GridState spec.height spec.width) :
    gridStateDistance spec
        (canonicalLevelRun data spec state)
        (canonicalProxyLevelRun data spec τ state) ≤
      canonicalOneStepRunSeries
        data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear spec := by
  simpa [gridStateDistance_self]
    using canonicalLevelRun_exact_vs_proxy_le
      data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear spec state state

noncomputable def canonicalLevelRunW :
    ProxySimulationWitness (fun spec => GridState spec.height spec.width) where
  resize := fun {src dst} state => resizeSomeGridState dst ⟨src, state⟩
  run := canonicalLevelRun data
  proxyRun := fun spec => canonicalProxyLevelRun data spec τ
  dist := gridStateDistance
  gain := fun spec => gain spec ^ spec.iterations
  runGap := fun spec =>
    canonicalOneStepRunSeries
      data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear spec
  dist_nonneg := gridStateDistance_nonneg
  dist_triangle := gridStateDistance_triangle
  gain_nonneg := fun spec => pow_nonneg (hgain_nonneg spec) spec.iterations
  runGap_nonneg := fun spec =>
    ProxySimulationWitness.iterateRunSeries_nonneg
      (canonicalOneStepW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      spec spec.iterations
  resize_dist_le := fun src dst x y => gridStateDistance_resizeSomeGridState_le src dst x y
  run_lipschitz := canonicalLevelRun_lipschitz
    data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear
  run_proxy_gap := canonicalLevelRun_exact_vs_proxy_le_same_seed
    data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear

noncomputable abbrev canonicalMultilevelRunSeries (levels : List RealLevelSpec) : ℝ :=
  ProxySimulationWitness.runSeries (canonicalLevelRunW data gain τ hgain_nonneg hτ
    hheight hwidth hgrid hgain himage hnear) levels

@[simp] theorem canonicalLevelRunW_exactStep_eq
    (spec : RealLevelSpec)
    (state : SomeGridState) :
    ProxySimulationWitness.exactMultilevelStep
      (canonicalLevelRunW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      spec state =
    multilevelStep (gridDataFamilyBuilder data) spec state := by
  rcases state with ⟨src, srcState⟩
  rfl

@[simp] theorem canonicalLevelRunW_proxyStep_eq
    (spec : RealLevelSpec)
    (state : SomeGridState) :
    ProxySimulationWitness.proxyMultilevelStep
      (canonicalLevelRunW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      spec state =
    canonicalProxyMultilevelStep data τ spec state := by
  rcases state with ⟨src, srcState⟩
  rfl

@[simp] theorem canonicalLevelRunW_exactRun_eq
    (seed : SomeGridState)
    (levels : List RealLevelSpec) :
    ProxySimulationWitness.exactMultilevelRun
      (canonicalLevelRunW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      seed levels =
    multilevelRun (gridDataFamilyBuilder data) seed levels := by
  induction levels generalizing seed with
  | nil =>
      rfl
  | cons spec rest ih =>
      simp [ProxySimulationWitness.exactMultilevelRun_cons, multilevelRun_cons, ih]

@[simp] theorem canonicalLevelRunW_proxyRun_eq
    (seed : SomeGridState)
    (levels : List RealLevelSpec) :
    ProxySimulationWitness.proxyMultilevelRun
      (canonicalLevelRunW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      seed levels =
    canonicalProxyMultilevelRun data τ seed levels := by
  induction levels generalizing seed with
  | nil =>
      rfl
  | cons spec rest ih =>
      simp [ProxySimulationWitness.proxyMultilevelRun_cons, canonicalProxyMultilevelRun, ih]

theorem canonical_multilevel_exact_proxy_same_spec
    (src : RealLevelSpec)
    (state : GridState src.height src.width)
    (levels : List RealLevelSpec) :
    (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).1 =
      (canonicalProxyMultilevelRun data τ ⟨src, state⟩ levels).1 := by
  simpa [canonicalLevelRunW_exactRun_eq, canonicalLevelRunW_proxyRun_eq]
    using ProxySimulationWitness.exact_proxy_same_spec
      (canonicalLevelRunW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      src state state levels

theorem canonical_multilevel_exact_vs_proxy_le
    (src : RealLevelSpec)
    (state : GridState src.height src.width)
    (levels : List RealLevelSpec) :
    gridStateDistance (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).1
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).2
        (cast (by
          simpa using congrArg
            (fun spec : RealLevelSpec => GridState spec.height spec.width)
            ((canonical_multilevel_exact_proxy_same_spec
              data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear src state
              levels).symm))
          (canonicalProxyMultilevelRun data τ ⟨src, state⟩ levels).2) ≤
      canonicalMultilevelRunSeries
        data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear levels := by
  have hmain :=
    ProxySimulationWitness.exact_vs_proxy_multilevel_le
      (canonicalLevelRunW data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear)
      src state state levels
  simpa [canonicalLevelRunW, canonicalLevelRunW_exactRun_eq, canonicalLevelRunW_proxyRun_eq,
      canonicalMultilevelRunSeries, gridStateDistance_self]
    using hmain

theorem canonical_single_level_exact_vs_proxy_le
    (src target : RealLevelSpec)
    (state : GridState src.height src.width) :
    gridStateDistance (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).2
        (cast (by
          simpa using congrArg
            (fun spec : RealLevelSpec => GridState spec.height spec.width)
            ((canonical_multilevel_exact_proxy_same_spec
              data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear src state
              [target]).symm))
          (canonicalProxyMultilevelRun data τ ⟨src, state⟩ [target]).2) ≤
      canonicalMultilevelRunSeries
        data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear [target] := by
  simpa using canonical_multilevel_exact_vs_proxy_le
    data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear src state [target]

theorem canonical_sameSize_exact_vs_proxy_le
    (spec : RealLevelSpec)
    (state : GridState spec.height spec.width) :
    gridStateDistance spec
        (canonicalLevelRun data spec state)
        (canonicalProxyLevelRun data spec τ state) ≤
      canonicalOneStepRunSeries
        data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear spec := by
  exact canonicalLevelRun_exact_vs_proxy_le_same_seed
    data gain τ hgain_nonneg hτ hheight hwidth hgrid hgain himage hnear spec state

end Simulation

end Canonical

end FastMLFE2.Theorems
