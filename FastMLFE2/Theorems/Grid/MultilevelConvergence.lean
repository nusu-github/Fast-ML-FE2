import FastMLFE2.Canonical.MultilevelRun

namespace FastMLFE2.Theorems

open FastMLFE2.Canonical

/-
Abstract coarse-to-fine convergence bounds.

The witness packages a per-level contractive run together with a transfer-gap bound for the
nearest-neighbor resize between successive levels. The resulting multilevel bound is affine in
the initial error: a product of gains times the initial error plus a weighted transfer series.
-/

abbrev SomeState (σ : RealLevelSpec → Type*) :=
  Σ spec : RealLevelSpec, σ spec

structure LevelConvergenceWitness (σ : RealLevelSpec → Type*) where
  resize : {src dst : RealLevelSpec} → σ src → σ dst
  run : (spec : RealLevelSpec) → σ spec → σ spec
  target : (spec : RealLevelSpec) → σ spec
  error : (spec : RealLevelSpec) → σ spec → ℝ
  gain : RealLevelSpec → ℝ
  transferGap : RealLevelSpec → RealLevelSpec → ℝ
  error_nonneg : ∀ spec state, 0 ≤ error spec state
  gain_nonneg : ∀ spec, 0 ≤ gain spec
  gain_lt_one : ∀ spec, gain spec < 1
  transferGap_nonneg : ∀ src dst, 0 ≤ transferGap src dst
  run_error_le : ∀ spec state,
    error spec (run spec state) ≤ gain spec * error spec state
  transfer_error_le : ∀ src dst (state : σ src),
    error dst (resize (src := src) (dst := dst) state) ≤
      error src state + transferGap src dst

namespace LevelConvergenceWitness

noncomputable def multilevelStep
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (target : RealLevelSpec)
    (state : SomeState σ) : SomeState σ := by
  rcases state with ⟨source, sourceState⟩
  exact ⟨target, W.run target (W.resize (src := source) (dst := target) sourceState)⟩

noncomputable def multilevelRun
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (seed : SomeState σ)
    (levels : List RealLevelSpec) : SomeState σ :=
  levels.foldl (fun state target => multilevelStep W target state) seed

def gainProduct
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ) : List RealLevelSpec → ℝ
  | [] => 1
  | target :: rest => W.gain target * gainProduct W rest

def transferSeries
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (src : RealLevelSpec) : List RealLevelSpec → ℝ
  | [] => 0
  | target :: rest =>
      gainProduct W rest * (W.gain target * W.transferGap src target) +
        transferSeries W target rest

@[simp] theorem multilevelRun_nil
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (seed : SomeState σ) :
    multilevelRun W seed [] = seed := by
  rfl

@[simp] theorem multilevelRun_cons
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (seed : SomeState σ)
    (target : RealLevelSpec)
    (levels : List RealLevelSpec) :
    multilevelRun W seed (target :: levels) =
      multilevelRun W (multilevelStep W target seed) levels := by
  rfl

theorem gainProduct_nonneg
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (levels : List RealLevelSpec) :
    0 ≤ gainProduct W levels := by
  induction levels with
  | nil =>
      simp [gainProduct]
  | cons target rest ih =>
      simp [gainProduct, W.gain_nonneg target, ih, mul_nonneg]

theorem transferSeries_nonneg
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (src : RealLevelSpec)
    (levels : List RealLevelSpec) :
    0 ≤ transferSeries W src levels := by
  induction levels generalizing src with
  | nil =>
      simp [transferSeries]
  | cons target rest ih =>
      have hprod : 0 ≤ gainProduct W rest := gainProduct_nonneg W rest
      have hterm : 0 ≤ gainProduct W rest * (W.gain target * W.transferGap src target) := by
        refine mul_nonneg hprod ?_
        exact mul_nonneg (W.gain_nonneg target) (W.transferGap_nonneg src target)
      simpa [transferSeries] using add_nonneg hterm (ih target)

theorem run_iterate_error_le
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (spec : RealLevelSpec)
    (k : Nat)
    (state : σ spec) :
    W.error spec ((Nat.iterate (W.run spec) k) state) ≤
      W.gain spec ^ k * W.error spec state := by
  induction k generalizing state with
  | zero =>
      simp
  | succ k ih =>
      calc
        W.error spec ((Nat.iterate (W.run spec) k) (W.run spec state))
            ≤ W.gain spec ^ k * W.error spec (W.run spec state) := ih _
        _ ≤ W.gain spec ^ k * (W.gain spec * W.error spec state) := by
              exact mul_le_mul_of_nonneg_left (W.run_error_le spec state)
                (pow_nonneg (W.gain_nonneg spec) _)
        _ = W.gain spec ^ (k + 1) * W.error spec state := by
              rw [pow_succ']
              ring

theorem multilevelStep_error_le
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (target : RealLevelSpec)
    (state : SomeState σ) :
    W.error target (multilevelStep W target state).2 ≤
      W.gain target * (W.error state.1 state.2 + W.transferGap state.1 target) := by
  rcases state with ⟨source, sourceState⟩
  change W.error target (W.run target (W.resize (src := source) (dst := target) sourceState)) ≤
    W.gain target * (W.error source sourceState + W.transferGap source target)
  calc
    W.error target (W.run target (W.resize (src := source) (dst := target) sourceState))
        ≤ W.gain target * W.error target (W.resize (src := source) (dst := target) sourceState) :=
          W.run_error_le target _
    _ ≤ W.gain target * (W.error source sourceState + W.transferGap source target) := by
          exact mul_le_mul_of_nonneg_left (W.transfer_error_le source target sourceState)
            (W.gain_nonneg target)

theorem multilevelRun_error_le
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (src : RealLevelSpec)
    (state : σ src)
    (levels : List RealLevelSpec) :
    W.error (multilevelRun W ⟨src, state⟩ levels).1 (multilevelRun W ⟨src, state⟩ levels).2 ≤
      gainProduct W levels * W.error src state + transferSeries W src levels := by
  induction levels generalizing src state with
  | nil =>
      simp [multilevelRun, gainProduct, transferSeries]
  | cons target rest ih =>
      have hstep :
          W.error target (W.run target (W.resize (src := src) (dst := target) state)) ≤
            W.gain target * (W.error src state + W.transferGap src target) := by
        simpa [multilevelStep] using multilevelStep_error_le W target ⟨src, state⟩
      have hrest :
          W.error (multilevelRun W
            ⟨target, W.run target (W.resize (src := src) (dst := target) state)⟩ rest).1
            (multilevelRun W
              ⟨target, W.run target (W.resize (src := src) (dst := target) state)⟩ rest).2 ≤
            gainProduct W rest *
                W.error target (W.run target (W.resize (src := src) (dst := target) state)) +
              transferSeries W target rest := by
        simpa using ih target (W.run target (W.resize (src := src) (dst := target) state))
      calc
        W.error (multilevelRun W ⟨src, state⟩ (target :: rest)).1
            (multilevelRun W ⟨src, state⟩ (target :: rest)).2
            = W.error (multilevelRun W
                ⟨target, W.run target (W.resize (src := src) (dst := target) state)⟩ rest).1
                (multilevelRun W
                  ⟨target, W.run target (W.resize (src := src) (dst := target) state)⟩ rest).2 := by
                  simp [multilevelRun, multilevelStep]
        _ ≤ gainProduct W rest *
              W.error target (W.run target (W.resize (src := src) (dst := target) state)) +
              transferSeries W target rest := hrest
        _ ≤ gainProduct W rest * (W.gain target * (W.error src state + W.transferGap src target)) +
              transferSeries W target rest := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hstep (gainProduct_nonneg W rest))
                  le_rfl
        _ = gainProduct W (target :: rest) * W.error src state +
              transferSeries W src (target :: rest) := by
              simp [gainProduct, transferSeries]
              ring

theorem multilevelRun_singleton_error_le
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (src target : RealLevelSpec)
    (state : σ src) :
    W.error (multilevelRun W ⟨src, state⟩ [target]).1
      (multilevelRun W ⟨src, state⟩ [target]).2 ≤
      W.gain target * W.error src state + W.gain target * W.transferGap src target := by
  simpa [gainProduct, transferSeries] using multilevelRun_error_le W src state [target]

theorem multilevelRun_singleton_error_le_of_zero_transfer
    {σ : RealLevelSpec → Type*}
    (W : LevelConvergenceWitness σ)
    (src target : RealLevelSpec)
    (state : σ src)
    (hgap : W.transferGap src target = 0) :
    W.error (multilevelRun W ⟨src, state⟩ [target]).1
      (multilevelRun W ⟨src, state⟩ [target]).2 ≤
      W.gain target * W.error src state := by
  simpa [hgap] using multilevelRun_singleton_error_le W src target state

end LevelConvergenceWitness

end FastMLFE2.Theorems
