import FastMLFE2.Canonical.MultilevelRun

namespace FastMLFE2.Theorems

open FastMLFE2.Canonical

abbrev ProxyState (σ : RealLevelSpec → Type*) :=
  Σ spec : RealLevelSpec, σ spec

structure ProxySimulationWitness (σ : RealLevelSpec → Type*) where
  resize : {src dst : RealLevelSpec} → σ src → σ dst
  run : (spec : RealLevelSpec) → σ spec → σ spec
  proxyRun : (spec : RealLevelSpec) → σ spec → σ spec
  dist : (spec : RealLevelSpec) → σ spec → σ spec → ℝ
  gain : RealLevelSpec → ℝ
  runGap : RealLevelSpec → ℝ
  dist_nonneg : ∀ spec x y, 0 ≤ dist spec x y
  dist_triangle : ∀ spec x y z, dist spec x z ≤ dist spec x y + dist spec y z
  gain_nonneg : ∀ spec, 0 ≤ gain spec
  runGap_nonneg : ∀ spec, 0 ≤ runGap spec
  resize_dist_le : ∀ src dst (x y : σ src),
    dist dst (resize (src := src) (dst := dst) x) (resize (src := src) (dst := dst) y) ≤
      dist src x y
  run_lipschitz : ∀ spec (x y : σ spec),
    dist spec (run spec x) (run spec y) ≤ gain spec * dist spec x y
  run_proxy_gap : ∀ spec (x : σ spec),
    dist spec (run spec x) (proxyRun spec x) ≤ runGap spec

namespace ProxySimulationWitness

noncomputable def exactMultilevelStep
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (target : RealLevelSpec)
    (state : ProxyState σ) : ProxyState σ := by
  rcases state with ⟨source, sourceState⟩
  exact ⟨target, W.run target (W.resize (src := source) (dst := target) sourceState)⟩

noncomputable def proxyMultilevelStep
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (target : RealLevelSpec)
    (state : ProxyState σ) : ProxyState σ := by
  rcases state with ⟨source, sourceState⟩
  exact ⟨target, W.proxyRun target (W.resize (src := source) (dst := target) sourceState)⟩

noncomputable def exactMultilevelRun
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (seed : ProxyState σ)
    (levels : List RealLevelSpec) : ProxyState σ :=
  levels.foldl (fun state target => exactMultilevelStep W target state) seed

noncomputable def proxyMultilevelRun
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (seed : ProxyState σ)
    (levels : List RealLevelSpec) : ProxyState σ :=
  levels.foldl (fun state target => proxyMultilevelStep W target state) seed

def gainProduct
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ) : List RealLevelSpec → ℝ
  | [] => 1
  | target :: rest => W.gain target * gainProduct W rest

def runSeries
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ) : List RealLevelSpec → ℝ
  | [] => 0
  | target :: rest =>
      gainProduct W rest * W.runGap target + runSeries W rest

def iterateRunSeries
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (spec : RealLevelSpec) : Nat → ℝ
  | 0 => 0
  | k + 1 => W.gain spec ^ k * W.runGap spec + iterateRunSeries W spec k

@[simp] theorem exactMultilevelRun_nil
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (seed : ProxyState σ) :
    exactMultilevelRun W seed [] = seed := by
  rfl

@[simp] theorem proxyMultilevelRun_nil
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (seed : ProxyState σ) :
    proxyMultilevelRun W seed [] = seed := by
  rfl

@[simp] theorem exactMultilevelRun_cons
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (seed : ProxyState σ)
    (target : RealLevelSpec)
    (levels : List RealLevelSpec) :
    exactMultilevelRun W seed (target :: levels) =
      exactMultilevelRun W (exactMultilevelStep W target seed) levels := by
  rfl

@[simp] theorem proxyMultilevelRun_cons
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (seed : ProxyState σ)
    (target : RealLevelSpec)
    (levels : List RealLevelSpec) :
    proxyMultilevelRun W seed (target :: levels) =
      proxyMultilevelRun W (proxyMultilevelStep W target seed) levels := by
  rfl

theorem gainProduct_nonneg
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (levels : List RealLevelSpec) :
    0 ≤ gainProduct W levels := by
  induction levels with
  | nil =>
      simp [gainProduct]
  | cons target rest ih =>
      simp [gainProduct, W.gain_nonneg target, ih, mul_nonneg]

theorem runSeries_nonneg
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (levels : List RealLevelSpec) :
    0 ≤ runSeries W levels := by
  induction levels with
  | nil =>
      simp [runSeries]
  | cons target rest ih =>
      have hprod : 0 ≤ gainProduct W rest := gainProduct_nonneg W rest
      have hterm : 0 ≤ gainProduct W rest * W.runGap target := by
        exact mul_nonneg hprod (W.runGap_nonneg target)
      simpa [runSeries] using add_nonneg hterm ih

theorem iterateRunSeries_nonneg
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (spec : RealLevelSpec)
    (k : Nat) :
    0 ≤ iterateRunSeries W spec k := by
  induction k with
  | zero =>
      simp [iterateRunSeries]
  | succ k ih =>
      exact add_nonneg
        (mul_nonneg (pow_nonneg (W.gain_nonneg spec) k) (W.runGap_nonneg spec))
        ih

theorem exact_vs_proxy_run_le
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (spec : RealLevelSpec)
    (x y : σ spec) :
    W.dist spec (W.run spec x) (W.proxyRun spec y) ≤
      W.gain spec * W.dist spec x y + W.runGap spec := by
  calc
    W.dist spec (W.run spec x) (W.proxyRun spec y)
      ≤ W.dist spec (W.run spec x) (W.run spec y) +
          W.dist spec (W.run spec y) (W.proxyRun spec y) := by
            exact W.dist_triangle spec _ _ _
    _ ≤ W.gain spec * W.dist spec x y + W.runGap spec := by
          exact add_le_add (W.run_lipschitz spec x y) (W.run_proxy_gap spec y)

theorem exact_vs_proxy_step_le
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (src target : RealLevelSpec)
    (x y : σ src) :
    W.dist target
        (exactMultilevelStep W target ⟨src, x⟩).2
        (proxyMultilevelStep W target ⟨src, y⟩).2 ≤
      W.gain target * W.dist src x y + W.runGap target := by
  change
    W.dist target
      (W.run target (W.resize (src := src) (dst := target) x))
      (W.proxyRun target (W.resize (src := src) (dst := target) y)) ≤
        W.gain target * W.dist src x y + W.runGap target
  calc
    W.dist target
        (W.run target (W.resize (src := src) (dst := target) x))
        (W.proxyRun target (W.resize (src := src) (dst := target) y))
      ≤ W.gain target *
          W.dist target (W.resize (src := src) (dst := target) x)
            (W.resize (src := src) (dst := target) y) + W.runGap target := by
          exact exact_vs_proxy_run_le W target _ _
    _ ≤ W.gain target * W.dist src x y + W.runGap target := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (W.resize_dist_le src target x y)
              (W.gain_nonneg target))
            le_rfl

theorem exact_proxy_same_spec
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (src : RealLevelSpec)
    (x y : σ src)
    (levels : List RealLevelSpec) :
    (exactMultilevelRun W ⟨src, x⟩ levels).1 =
      (proxyMultilevelRun W ⟨src, y⟩ levels).1 := by
  induction levels generalizing src x y with
  | nil =>
      rfl
  | cons target rest ih =>
      simpa using ih target
        (W.run target (W.resize (src := src) (dst := target) x))
        (W.proxyRun target (W.resize (src := src) (dst := target) y))

theorem exact_vs_proxy_iterate_le
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (spec : RealLevelSpec)
    (k : Nat)
    (x y : σ spec) :
    W.dist spec ((Nat.iterate (W.run spec) k) x) ((Nat.iterate (W.proxyRun spec) k) y) ≤
      W.gain spec ^ k * W.dist spec x y + iterateRunSeries W spec k := by
  induction k generalizing x y with
  | zero =>
      simp [iterateRunSeries]
  | succ k ih =>
      calc
        W.dist spec ((Nat.iterate (W.run spec) k) (W.run spec x))
            ((Nat.iterate (W.proxyRun spec) k) (W.proxyRun spec y))
          ≤ W.gain spec ^ k * W.dist spec (W.run spec x) (W.proxyRun spec y) +
              iterateRunSeries W spec k := ih _ _
        _ ≤ W.gain spec ^ k * (W.gain spec * W.dist spec x y + W.runGap spec) +
              iterateRunSeries W spec k := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left
                  (exact_vs_proxy_run_le W spec x y)
                  (pow_nonneg (W.gain_nonneg spec) k))
                le_rfl
        _ = W.gain spec ^ (k + 1) * W.dist spec x y + iterateRunSeries W spec (k + 1) := by
              simp [iterateRunSeries, pow_succ']
              ring

theorem run_iterate_lipschitz
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (spec : RealLevelSpec)
    (k : Nat)
    (x y : σ spec) :
    W.dist spec ((Nat.iterate (W.run spec) k) x) ((Nat.iterate (W.run spec) k) y) ≤
      W.gain spec ^ k * W.dist spec x y := by
  induction k generalizing x y with
  | zero =>
      simp
  | succ k ih =>
      calc
        W.dist spec ((Nat.iterate (W.run spec) k) (W.run spec x))
            ((Nat.iterate (W.run spec) k) (W.run spec y))
          ≤ W.gain spec ^ k * W.dist spec (W.run spec x) (W.run spec y) := ih _ _
        _ ≤ W.gain spec ^ k * (W.gain spec * W.dist spec x y) := by
              exact mul_le_mul_of_nonneg_left
                (W.run_lipschitz spec x y)
                (pow_nonneg (W.gain_nonneg spec) k)
        _ = W.gain spec ^ (k + 1) * W.dist spec x y := by
              rw [pow_succ']
              ring

theorem exact_vs_proxy_multilevel_le
    {σ : RealLevelSpec → Type*}
    (W : ProxySimulationWitness σ)
    (src : RealLevelSpec)
    (x y : σ src)
    (levels : List RealLevelSpec) :
    W.dist (exactMultilevelRun W ⟨src, x⟩ levels).1
        (exactMultilevelRun W ⟨src, x⟩ levels).2
        (cast (by
          simpa using congrArg σ (exact_proxy_same_spec W src x y levels).symm)
          (proxyMultilevelRun W ⟨src, y⟩ levels).2) ≤
      gainProduct W levels * W.dist src x y + runSeries W levels := by
  induction levels generalizing src x y with
  | nil =>
      simp [exactMultilevelRun, proxyMultilevelRun, gainProduct, runSeries]
  | cons target rest ih =>
      have hstep :
          W.dist target
              (exactMultilevelStep W target ⟨src, x⟩).2
              (proxyMultilevelStep W target ⟨src, y⟩).2 ≤
            W.gain target * W.dist src x y + W.runGap target :=
        exact_vs_proxy_step_le W src target x y
      have hrest :=
        ih target
          (W.run target (W.resize (src := src) (dst := target) x))
          (W.proxyRun target (W.resize (src := src) (dst := target) y))
      simpa [exactMultilevelRun_cons, proxyMultilevelRun_cons, gainProduct, runSeries] using
        calc
          W.dist
              (exactMultilevelRun W (exactMultilevelStep W target ⟨src, x⟩) rest).1
              (exactMultilevelRun W (exactMultilevelStep W target ⟨src, x⟩) rest).2
              (cast
                (by
                  simpa using congrArg σ
                    (exact_proxy_same_spec W target
                      (W.run target (W.resize (src := src) (dst := target) x))
                      (W.proxyRun target (W.resize (src := src) (dst := target) y))
                      rest).symm)
                (proxyMultilevelRun W (proxyMultilevelStep W target ⟨src, y⟩) rest).2)
            ≤ gainProduct W rest *
                W.dist target
                  (W.run target (W.resize (src := src) (dst := target) x))
                  (W.proxyRun target (W.resize (src := src) (dst := target) y)) +
              runSeries W rest := hrest
          _ ≤ gainProduct W rest * (W.gain target * W.dist src x y + W.runGap target) +
                runSeries W rest := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hstep (gainProduct_nonneg W rest))
                    le_rfl
          _ = gainProduct W (target :: rest) * W.dist src x y + runSeries W (target :: rest) := by
                simp [gainProduct, runSeries]
                ring

end ProxySimulationWitness

end FastMLFE2.Theorems
