# FastMLFE2 リファクタリング計画

> 作成日: 2026-03-28
> 対象: FastMLFE2 Lean 4 形式化プロジェクト (5,999行 / 定理44ファイル + 定義層3,034行)
> 目的: 証明間の関係性整理・有効性見直し・MathLib活用方針の策定

---

## 現状サマリー

| 指標 | 値 | 評価 |
|------|------|------|
| 定理ファイル数 | 44 | — |
| 定理層 総行数 | 5,999 | — |
| 定義層 総行数 | 3,034 | — |
| `sorry` 使用数 | **0** | ✅ 全証明完了 |
| `axiom` 宣言数 | **0** | ✅ 不当な公理なし |
| `maxHeartbeats` 設定数 | **0** | ✅ パフォーマンス問題なし |
| レイヤリング違反 | **3** | ⚠️ 修正必要 |
| デッドエンド定理 | **19/44 (43%)** | ⚠️ 接続性改善の余地 |
| 未接続リンク | **4** | ⚠️ 論理的接続が不足 |
| コンパイル不能ファイル | **2** (GlobalSystem, MultigridSpec) | ❌ 削除/隔離必要 |

---

## A. 証明の正当性・完全性

### 現状

プロジェクト全体の `sorry` = 0、`axiom` = 0 であり、44ファイルの全証明が完了している。
`Assumptions.Bundles` の typeclass パラメータ化により、仮定が明示的に管理されている。

### 問題点

#### A-1. デッドエンド定理が多い (19/44 = 43%)

44ファイル中19ファイルが他の定理ファイルから参照されていない。カテゴリ別:

**純粋孤立 (7ファイル)** — 他の定理と接続なし:
- `SpatialDecay`, `ContinuousGrad`, `DiscreteGrad`, `Grid`, `Jacobi`, `ForegroundMetrics`, `FixedPrecisionMultilevel`

**終端出力 (12ファイル)** — 他の定理を使うが、自身は使われない:
- `BinaryAlphaCost`, `BleedThrough`, `BlurFusionFixedPoint`, `ClampPlacementCounterexample`, `FixedPrecisionCost`, `FixedPrecisionWraparound`, `InteriorKernel`, `IterationInvariance`, `NearBinaryCounterexample`, `NormalizedWeights`, `PropagationRadius`, `ResidualCompositeBounds`

**評価**: 反例ファイル4つ (`*Counterexample`, `BlurFusionFixedPoint`, `FixedPrecisionWraparound`) は終端であること自体が正しい。評価系3ファイル (`ForegroundMetrics`, `ContinuousGrad`, `DiscreteGrad`) もメトリクス定義の性質上終端で問題ない。しかし、以下は **接続すべき**:

| ファイル | 接続先候補 | 理由 |
|----------|-----------|------|
| `SpatialDecay` | `PropagationRadius` | 抽象decay interface → 具体的Jacobi伝播 |
| `IterationInvariance` | `FixedPrecisionCost` | 係数キャッシュ正当性 → FPコストモデル |
| `ContractionBounds` | `JacobiContraction` | 汎用緩和理論 → Jacobi特化 |
| `NormalizedWeights` | `NearBinary` | 正規化重み特性 → 近似バイナリ補正 |
| `BinaryAlphaCost` | Stage 3 refinement chain | コスト形式 → 実装導出 |

#### A-2. 未接続の論理リンク (4箇所)

前回分析から **全4箇所が未接続のまま**:

1. **SpatialDecay ↔ PropagationRadius**: `RadiusDecay`/`HaloDecay` インターフェースが `propagationNeighborhood` 成長則と未接続。`jacobiSpectralRadius` を decay rate `ρ` として instantiate すれば、定量的空間減衰定理が得られる。
2. **IterationInvariance → FixedPrecision**: 係数キャッシュの状態非依存性が FP コストモデルの逆数テーブル再利用を正当化するはずだが、形式的引用なし。
3. **ContractionBounds → JacobiContraction**: Jacobi反復が `r=1` の relaxed update であることを示す定理がない。`BleedThrough` は両方を使うが、接続定理は存在しない。
4. **NormalizedWeights → NearBinary**: 正規化重み特性が `foregroundMean`/`backgroundMean` の推論を簡素化できるはずだが、`NearBinary` は生の定義から直接推論している。

#### A-3. ハブ定理の依存集中

`ClosedForm` が7ファイルから参照されるハブ。しかし定義 (`closedFormSolution` 等) と定理が混在しており、レイヤリング違反の原因にもなっている。

### 改善案

| ID | 改善 | 優先度 |
|----|------|--------|
| A-1a | 4つの未接続リンクを接続する定理を追加 | **高** |
| A-1b | `BinaryAlphaCost` を Stage 3 チェーンに接続 | 中 |
| A-2 | `ClosedForm` から定義を `Core.ClosedForm` に抽出 | **高** |
| A-3 | `NearBinary.lean` を定義モジュールと定理モジュールに分割 | 中 |

---

## B. MathLib活用度

### 現状

依存グラフは Mathlib v4.28.0 上に構築。`Matrix.det_fin_two`, `Matrix.nonsing_inv`, `Int.floor` 等の基本 API は活用済み。

### 問題点

#### B-1. 独自実装が MathLib に既存

| ファイル | 独自定義 | MathLib代替 | 推定削減行数 | 難度 |
|----------|----------|-------------|-------------|------|
| `ClampLocal` | `clamp01Scalar` = `max 0 (min 1 x)` | `Set.projIcc 0 1` + `projIcc_nonexpansive` | ~12行 | **低** |
| `ContractionBounds` | `relaxedUpdate`, `relaxationContractionRate`, `relaxationLambdaMax` (67行) | `ContractingWith` API (`Topology.MetricSpace.Contracting`) | ~50-70行 (ただし型変換コスト有) | **高** |
| `QuantizationBounds` | `gridQuantize` = `Int.floor(x*S)/S` | **既に `Int.floor` 使用済み** ✅。`geomSeries` は `Finset.geom_sum_def` で置換可能 | ~10行 | 低 |

#### B-2. 命名規則

✅ **完全準拠**: 定理名は全て `snake_case`、構造体名は全て `CamelCase`。違反なし。

#### B-3. `Set.projIcc` への移行 (最優先)

`clamp01Scalar x` ≡ `Set.projIcc 0 1 x` であり、以下の MathLib 定理が直接使用可能:
- `projIcc_of_mem` → `clamp01Scalar_eq_self_of_mem_Icc` を置換
- `projIcc_nonexpansive` → カスタム非拡大性証明を置換

**作業量**: 小 (ClampLocal.lean 62行のうち ~12行を削減可能)
**効果**: `ClampPlacement`, `ClosedFormBox`, `NearBinaryCounterexample` の下流定理も簡素化

#### B-4. `ContractingWith` への移行 (中優先)

MathLib の `ContractingWith` API は以下を提供:
- `ContractingWith.exists_unique_fixed_point` — 不動点の存在と一意性
- `ContractingWith.dist_fixedPoint_le` — 不動点への距離上界
- `tsum_geometric_of_lt_one` — 幾何級数の和

**課題**: `EMetricSpace` フレームワークへの型変換が必要。`relaxedUpdate` の `NormedAddCommGroup` → `EMetricSpace` リフティングが主要コスト。
**効果**: ~50行削減 + より強力な収束定理へのアクセス

### 改善案

| ID | 改善 | 優先度 |
|----|------|--------|
| B-1 | `clamp01Scalar` → `Set.projIcc` 移行 | **高** |
| B-2 | `ContractionBounds` → `ContractingWith` 移行 | 中 |
| B-3 | `geomSeries` → MathLib `Finset.geom_sum_def` 移行 | 低 |

---

## C. 定義品質

### 現状

- 定義層 3,034行、`noncomputable def` 156個 (全て実数演算のため正当)
- `@[simp]` 165個 (定義層132、定理層33) — 適切に分散
- `DecidableEq` は設定型のみに限定 (数学的対象には未使用) ✅

### 問題点

#### C-1. 定理ファイルに混在する定義

**`JacobiContraction.lean` (351行)**:
- 12個の `noncomputable def` が定理と混在
- `jacobiDiagForeground`, `jacobiDiagBackground`, `jacobiCrossTerm`, `jacobiForegroundCoeff`, `jacobiBackgroundCoeff`, `jacobiStep`, `jacobiDifferenceMap`, `localInfinityNorm`, `jacobiSpectralRadiusSq`, `jacobiSpectralRadius`, `jacobiIterate`, `jacobiOneStepGain`
- これらは **定義** であり、`Core.JacobiIteration` または `Level.JacobiIteration` に属すべき

**`NearBinary.lean` (554行)**:
- 2個の定義 (`binaryZeroCtx`, `weightDriftBudget`) が24定理と混在
- 定義数は少ないが、ファイル長が突出 (他の最長ファイルの1.57倍)

**`ClosedForm.lean` (136行)**:
- `closedFormSolution`, `closedFormDenom`, `closedFormForegroundNumerator`, `closedFormBackgroundNumerator`, `inverseSolution` が定理と混在
- これが `Level.Jacobi` からの逆参照 (レイヤリング違反) の根本原因

#### C-2. Bundled/Unbundled 選択

✅ 適切。`LocalContext` は unbundled structure (フィールドアクセスが多いため)、`CoreMathAssumptions` は bundled typeclass (仮定の一括注入のため)。問題なし。

#### C-3. 型クラス継承の深さ

✅ `maxSynthPendingDepth = 3` で制御済み。`maxHeartbeats` 超過なし。

### 改善案

| ID | 改善 | 優先度 |
|----|------|--------|
| C-1a | `ClosedForm` の定義を `Core.ClosedForm` に抽出 (A-2 と同一) | **高** |
| C-1b | `JacobiContraction` の12定義を `Level.JacobiIteration` に抽出 | **高** |
| C-1c | `NearBinary` を定義+定理に分割 (554行 → ~100行定義 + ~454行定理) | 中 |
| C-2 | `ContractionBounds` の `relaxedUpdate` 等を utility モジュールに抽出 | 中 |

---

## D. 証明スタイル

### 現状

- `have` : `suffices` = 403 : 2 (99.5% have)
- `calc` チェーン + `ring` + `field_simp` + `linarith`/`nlinarith` パターンが一貫
- `@[simp]` は Core 層 (34個) に集中、定理層は控えめ (33個)

### 問題点

#### D-1. `suffices` の過少使用

`suffices` が `CostToNormalEquation.lean` の2箇所のみ。`have` で十分な場合が多いが、**ゴール変換が主目的**のケースでは `suffices` の方が意図が明確。

→ 機械的に置換すべきではないが、長い `have` チェーン (特に `NearBinary` の74箇所) ではゴールの変形目的の `have` を `suffices` に置換することで可読性向上の余地あり。

#### D-2. `NearBinary.lean` の `have` 過多

74個の `have` ステートメントは44ファイル中最多。構造化のためのセクションコメントや `section` ブロックの追加で可読性を改善可能。

#### D-3. Tactic/Term-mode の一貫性

✅ ほぼ一貫。短い等式は `by simp [...]` または `by ring`、複雑な証明は tactic mode で `have`/`calc` チェーン。問題なし。

### 改善案

| ID | 改善 | 優先度 |
|----|------|--------|
| D-1 | `NearBinary.lean` にセクション構造を追加 | 低 |
| D-2 | ゴール変形目的の `have` → `suffices` 置換 (選択的) | 低 |

---

## E. パフォーマンス

### 現状

- `maxHeartbeats` 超過: **0箇所** ✅
- `maxSynthPendingDepth = 3` で typeclass 合成を制限済み
- 循環 import: なし (DAG 構造確認済み)

### 問題点

#### E-1. コンパイル不能ファイル

`GlobalSystem.lean` (294行) と `MultigridSpec.lean` (120行) が存在しないモジュール (`FastMLFE2.ConcreteImage`, `FastMLFE2.NormalEquation`) を import しており、コンパイル不能。

→ umbrella file (`FastMLFE2.lean`) には含まれていないため `lake build` には影響しないが、リポジトリ内にデッドコードとして残存。

#### E-2. 並列ビルド阻害

`ClosedForm.lean` が7ファイルのハブであり、ここがボトルネック。定義抽出 (C-1a) により `Core.ClosedForm` → `Level.Jacobi` の依存が短くなり、間接的にビルド並列性が向上する。

#### E-3. import グラフの不必要な依存

- `FixedPrecision/Coefficients.lean` → `Theorems.QuantizationBounds` (stale)
- `FixedPrecision/LocalSolver.lean` → `Theorems.ClosedFormMeanResidual` (stale)
- これらの stale import は不必要なリビルドを引き起こす可能性あり

### 改善案

| ID | 改善 | 優先度 |
|----|------|--------|
| E-1 | `GlobalSystem.lean` / `MultigridSpec.lean` を削除 or `Experimental/` に隔離 | **高** |
| E-2 | stale import 2箇所を除去 | **高** |
| E-3 | `ClosedForm` 定義抽出によるハブ分散 | **高** (C-1a と同一) |

---

## 構造改善提案

### Theorems/ サブディレクトリ構造 (44ファイル → 7サブディレクトリ)

```
Theorems/
  Foundation/          -- 基礎定理 (10ファイル)
    Invertibility, CostToNormalEquation, ClosedForm, ClosedFormBox,
    ClosedFormBoxInput, ClosedFormMeanResidual, NormalizedWeights,
    ClampLocal, CompositingError, MeanResidualBounds

  Iteration/           -- 反復収束理論 (10ファイル)
    Conditioning, JacobiContraction, ContractionBounds, BleedThrough,
    ClampPlacement, ResidualCompositeBounds, NearBinary, SpatialDecay,
    PropagationRadius, IterationInvariance

  DesignSpace/         -- 設計空間探索 (4ファイル)
    BinaryAlpha, BinaryAlphaCost, ChannelReuse, BlurFusionGap

  Grid/                -- 格子幾何 (8ファイル)
    Grid, GridNonempty, GridAssumptions, GridLocal,
    InteriorKernel, CanonicalBuilder, Jacobi, Locality

  FixedPrecision/      -- 固定精度精緻化 (5ファイル)
    QuantizationBounds, FixedPrecisionLocal, FixedPrecisionJacobi,
    FixedPrecisionCost, FixedPrecisionMultilevel

  Evaluation/          -- 評価メトリクス (3ファイル)
    ForegroundMetrics, ContinuousGrad, DiscreteGrad

  Counterexamples/     -- 反例 (4ファイル)
    NearBinaryCounterexample, ClampPlacementCounterexample,
    BlurFusionFixedPoint, FixedPrecisionWraparound
```

**リスク**: 全 import パスの更新が必要。`lake build` が通ることをバッチごとに確認する必要がある。

**判断**: Phase 3 で実施。Phase 0-2 の定義抽出・MathLib 移行が先。

---

## フェーズ別実行計画

### Phase 0 — ハウスキーピング

**ゴール**: デッドコード除去・stale import 修正

| タスク | 内容 | ゲート |
|--------|------|--------|
| 0-1 | `FixedPrecision/Coefficients.lean` から `Theorems.QuantizationBounds` import を除去 | `lake build` |
| 0-2 | `FixedPrecision/LocalSolver.lean` から `Theorems.ClosedFormMeanResidual` import を除去 | `lake build` |
| 0-3 | `GlobalSystem.lean` と `MultigridSpec.lean` を削除 (or `Experimental/` に移動) | `lake build` |

### Phase 1 — 定義抽出 (レイヤリング違反解消)

**ゴール**: 定理ファイルから定義を抽出し、レイヤリング違反を解消

| タスク | 内容 | ゲート |
|--------|------|--------|
| 1-1 | `Core.ClosedForm` モジュールを新規作成。`closedFormSolution`, `closedFormDenom`, `closedFormForegroundNumerator`, `closedFormBackgroundNumerator`, `inverseSolution` を `Theorems.ClosedForm` から移動 | `lake build` |
| 1-2 | `Level.Jacobi` を `Core.ClosedForm` から import するよう更新 (Theorems.ClosedForm への依存を除去) | `lake build` |
| 1-3 | `Theorems.ClosedForm` を `Core.ClosedForm` から import するよう更新 (定理のみ残す) | `lake build` |
| 1-4 | `Level.JacobiIteration` モジュールを新規作成。`JacobiContraction.lean` から12個の定義 (`jacobiStep`, `jacobiIterate`, `jacobiSpectralRadius` 等) を移動 | `lake build` |
| 1-5 | `NearBinary.lean` から `binaryZeroCtx`, `weightDriftBudget` を適切なモジュールに抽出 (or 同ファイル内でセクション整理) | `lake build` |

### Phase 2 — MathLib 移行

**ゴール**: 独自実装を MathLib 既存機能で置換

| タスク | 内容 | ゲート |
|--------|------|--------|
| 2-1 | `clamp01Scalar` → `Set.projIcc 0 1` に移行。`ClampLocal.lean` の非拡大性証明を `projIcc_nonexpansive` で置換 | `lake build` |
| 2-2 | `ContractionBounds` の relaxation theory → MathLib `ContractingWith` API に移行 (要: 型変換レイヤー設計) | `lake build` |
| 2-3 | `QuantizationBounds.geomSeries` → MathLib `Finset.geom_sum_def` に置換 | `lake build` |

### Phase 3 — 構造改善

**ゴール**: Theorems/ をサブディレクトリに整理

| タスク | 内容 | ゲート |
|--------|------|--------|
| 3-1 | Foundation/ サブディレクトリ作成・ファイル移動 (10ファイル) | `lake build` |
| 3-2 | Iteration/ サブディレクトリ作成・ファイル移動 (10ファイル) | `lake build` |
| 3-3 | 残り5サブディレクトリ (DesignSpace, Grid, FixedPrecision, Evaluation, Counterexamples) を作成・移動 | `lake build` |
| 3-4 | `FastMLFE2.lean` umbrella import パスを全更新 | `lake build` |
| 3-5 | `docs/architecture.md` を更新 | — |

### Phase 4 — 未接続リンクの接続

**ゴール**: 論理的に接続されるべき定理間のブリッジ定理を追加

| タスク | 内容 | ゲート |
|--------|------|--------|
| 4-1 | `SpatialDecay` → `PropagationRadius`: `RadiusDecay` を Jacobi 伝播で instantiate | `lake build` |
| 4-2 | `IterationInvariance` → `FixedPrecisionCost`: 係数キャッシュ正当性の形式的引用 | `lake build` |
| 4-3 | `ContractionBounds` → `JacobiContraction`: Jacobi を `r=1` relaxed update として接続 | `lake build` |
| 4-4 | `NormalizedWeights` → `NearBinary`: 正規化重み特性を NearBinary で活用 | `lake build` |

### Phase 5 — 証明簡素化 (継続的)

| タスク | 内容 | ゲート |
|--------|------|--------|
| 5-1 | `NearBinary.lean` の `have` チェーン (74箇所) にセクション構造追加 | `lake build` |
| 5-2 | `@[simp]` lemma の監査 (33個, 定理層): 競合する rewrite がないか確認 | `lake build` |
| 5-3 | 冗長な `nlinarith` を特定 lemma 適用に置換 (選択的) | `lake build` |

---

## 優先度マトリクス

```
           低コスト          高コスト
高効果  ┌────────────────┬────────────────┐
        │ Phase 0 全体   │ Phase 1 (1-1   │
        │ Phase 2 (2-1)  │  ~ 1-4)        │
        │ Phase 4 (4-2,  │ Phase 2 (2-2)  │
        │  4-3)          │ Phase 3 全体   │
        ├────────────────┼────────────────┤
低効果  │ Phase 5 (5-1)  │ Phase 4 (4-1,  │
        │ Phase 2 (2-3)  │  4-4)          │
        │ Phase 5 (5-2)  │                │
        └────────────────┴────────────────┘
```

**推奨実行順序**: Phase 0 → Phase 1 → Phase 2-1 → Phase 4-2,4-3 → Phase 2-2 → Phase 3 → Phase 4-1,4-4 → Phase 5

---

## 前回分析からの差分

| 項目 | 前回分析 | 今回確認結果 |
|------|----------|-------------|
| レイヤリング違反 3箇所 | 確認 | **全3箇所そのまま残存** |
| 未接続リンク 4箇所 | 確認 | **全4箇所未接続のまま** |
| GlobalSystem/MultigridSpec | 削除/隔離推奨 | **そのまま残存 (コンパイル不能)** |
| stale import 2箇所 | 除去推奨 | **そのまま残存** |
| NearBinary 分割 | 推奨 | **554行のまま (変更なし)** |
| MathLib `Set.projIcc` 移行 | 推奨 | **未実施** |
| Theorems/ サブディレクトリ化 | 推奨 | **未実施** |

→ 前回分析で指摘された全改善点が未着手。今回の計画で優先度付けし、フェーズ化して実行する。
