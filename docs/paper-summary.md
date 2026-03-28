# Paper Summary

A condensed overview of the mathematics in Germer et al.,
"Fast Multi-Level Foreground Estimation" (ICPR 2020,
[arXiv:2006.14970](https://arxiv.org/abs/2006.14970),
[DOI:10.1109/ICPR48806.2021.9412408](https://doi.org/10.1109/ICPR48806.2021.9412408)).
For full details — related work, qualitative figures, dataset preparation, and runtime
benchmarks — see the [original paper](https://arxiv.org/abs/2006.14970).

---

## 1. Problem Statement

Given a color image $I$ and an alpha matte $\alpha$, recover the foreground $F$ and
background $B$ satisfying the **compositing equation**:

$$I = \alpha F + (1 - \alpha) B$$

A naive composite $I^{\text{new}} = \alpha I + (1-\alpha) B^{\text{new}}$ works only when
$\alpha$ is near-binary; otherwise the old background bleeds through translucent regions.

> **Lean:** `Compositing.OneChannel` defines `compose α F B = α·F + (1-α)·B` with simp
> lemmas for $\alpha = 0$, $\alpha = 1$, and algebraic difference identities.

## 2. Global Cost Function (Levin et al.)

The starting point is the global cost from closed-form color estimation (Levin et al. 2007):

$$\mathcal{L}_{\text{global}}(F, B) = \sum_{i} \sum_c \left[\alpha_i F_i^c + (1-\alpha_i) B_i^c - I_i^c\right]^2 + |\alpha_{i_x}|\left[(F_{i_x}^c)^2 + (B_{i_x}^c)^2\right] + |\alpha_{i_y}|\left[(F_{i_y}^c)^2 + (B_{i_y}^c)^2\right]$$

Solving this requires a $2n \times 2n$ sparse linear system — too slow for interactive use
(~30s per channel at 0.4 MP).

## 3. Local Cost Function

The paper's core contribution replaces the global system with a **per-pixel local cost**.
For pixel $i$ and color channel $c$, with neighbors $j \in N_i$:

$$\mathcal{L}_{\text{local}}(F_i^c, B_i^c) = \underbrace{(\alpha_i F_i^c + (1-\alpha_i) B_i^c - I_i^c)^2}_{\text{compositing fidelity}} + \sum_{j \in N_i} \underbrace{(\epsilon_r + \omega|\alpha_i - \alpha_j|)}_{\text{neighbor weight } w_j} \left[(F_i^c - F_j^c)^2 + (B_i^c - B_j^c)^2\right]$$

- $\epsilon_r > 0$: regularization ensuring the problem is well-defined even when $\alpha$
  is constant (default $5 \times 10^{-3}$).
- $\omega \geq 0$: controls the influence of the alpha gradient (default $0.1$).
- $N_i$: four-connected neighbors (up, down, left, right).

> **Lean:** `Core.LocalEquation` defines `LocalContext` (carrying $\alpha_i$, $I_i^c$,
> neighbor data, $\epsilon_r$, $\omega$), the `localCost` function, the `normalMatrix` (2×2),
> and the `rhs` vector.

## 4. Matrix Form and Normal Equation

Introducing the unknowns $g_i^c = [F_i^c,\, B_i^c]^T$ and:

| Symbol  | Definition                                           | Size                |
| ------- | ---------------------------------------------------- | ------------------- |
| $U_i$   | $[\alpha_i,\; 1-\alpha_i]^T$                         | $2 \times 1$        |
| $h_i^c$ | stacked neighbor F and B values                      | $2                  |N_i| \times 1$
| $R$     | broadcast matrix (repeats $g_i^c$ for each neighbor) | $2                  |N_i| \times 2$
| $V_i$   | block-diagonal weight matrix $\text{diag}(S_i, S_i)$ | $2                  |N_i| \times 2|N_i|$
| $S_i$   | $\text{diag}(\epsilon_r + \omega                     | \alpha_i - \alpha_j |)_{j \in N_i}$ | $|N_i| \times |N_i|$

The cost becomes:

$$\mathcal{L}_{\text{local}}(g_i^c) = (U_i^T g_i^c - I_i^c)^2 + (R g_i^c - h_i^c)^T V_i (R g_i^c - h_i^c)$$

Setting $\frac{1}{2}\frac{\partial \mathcal{L}}{\partial g_i^c} = 0$ yields the **normal equation**:

$$g_i^c = \underbrace{(U_i U_i^T + R^T V_i R)^{-1}}_{\text{2×2 matrix, independent of } c} (I_i^c U_i + R^T V_i h_i^c)$$

### Key observation: channel independence

The matrix $A_i = U_i U_i^T + R^T V_i R$ depends only on $\alpha$ and the weights, **not**
on the color channel $c$. It needs to be computed and inverted only once per pixel, then
reused for R, G, B.

> **Lean:**
>
> - `Core.LocalSemantics` defines `SolvesNormalEquation`, `IsLocalSolution`,
>   `IsCostStationary`.
> - `Theorems.CostToNormalEquation` proves the bridge: $\text{IsCostStationary}
>   \iff \text{SolvesNormalEquation}$ via genuine `HasDerivAt` derivatives.
> - `Theorems.ChannelReuse` proves channel-independence via `SameWeightData`.

## 5. Explicit 2×2 Inverse

Since $A_i$ is $2 \times 2$, the inverse is computed analytically. Writing
$s = \sum_j w_j$ (total neighbor weight):

$$A_i = \begin{bmatrix} \alpha_i^2 + s & \alpha_i(1-\alpha_i) \\ \alpha_i(1-\alpha_i) & (1-\alpha_i)^2 + s \end{bmatrix}$$

$$\det(A_i) = s^2 + s\bigl[\alpha_i^2 + (1-\alpha_i)^2\bigr] > 0 \quad \text{(when } s > 0 \text{)}$$

The closed-form solution is then $g_i^c = A_i^{-1} b_i^c$ via the standard $2 \times 2$
inverse formula.

> **Lean:**
>
> - `Theorems.Invertibility` proves $\det(A_i) > 0$ and `IsUnit` under
>   `CoreMathAssumptions` ($\epsilon_r > 0$, neighbors nonempty).
> - `Theorems.ClosedForm` gives the explicit inverse formula and proves uniqueness.
> - `Theorems.Conditioning` decomposes $A_i = s \cdot I + u \cdot u^T$ (rank-1 update),
>   derives exact eigenvalues $s$ and $s + q(\alpha)$ where $q(\alpha) = \alpha^2 + (1-\alpha)^2$,
>   and bounds the condition number $\kappa = 1 + q(\alpha)/s$.

## 6. Multi-Level Algorithm

A single pass of the local solver propagates information only to immediate neighbors. The
paper addresses this with a **coarse-to-fine pyramid**:

1. Initialize $F$ and $B$ at $1 \times 1$.
2. Compute the number of levels: $n_l = \lceil \log_2(\max(\hat{w}, \hat{h})) \rceil$.
3. For each level $l = 1, \ldots, n_l$:
   - Compute working size: $w = \text{round}(\hat{w}^{l/n_l})$,
     $h = \text{round}(\hat{h}^{l/n_l})$.
   - Resize $I$, $\alpha$, $F$, $B$ to $(w, h)$ via nearest-neighbor interpolation.
   - Iterate: for each pixel $i$, build $A_i$ by accumulating neighbor weights, solve
     $g_i^c = A_i^{-1} b_i^c$, and clamp to $[0, 1]$.
   - Apply the update simultaneously to all pixels (Jacobi-style).
4. Return $F$, $B$ at full resolution.

**Default parameters:** $\epsilon_r = 5 \times 10^{-3}$, $\omega = 0.1$,
$N_i$ = 4-connected with boundary clamping, more iterations at low resolution (10 below
$32 \times 32$, 2 at higher resolutions).

> **Lean:**
>
> - `Canonical.MultilevelSchedule` formalizes `levelSizes` using the $\hat{w}^{l/n_l}$
>   interpolation.
> - `Canonical.Grid` models `Fin h × Fin w` geometry with boundary-aware four-connected
>   neighborhoods.
> - `Level.Jacobi` defines `jacobiStep` (simultaneous update) and
>   `Level.Locality` captures the neighborhood dependence.
> - `Theorems.Jacobi` proves each updated pixel solves its local normal equation.
> - `Theorems.PropagationRadius` bounds $k$-pass propagation radius.
> - `Theorems.ClampPlacement` and `Theorems.ClampPlacementCounterexample` analyze
>   where the $[0,1]$ clamp is applied (inside vs. end of iteration).

## 7. Special Cases Formalized

The Lean formalization proves several structural results that correspond to simplifications
noted (or implied) in the paper:

| Paper Observation                                          | Lean Theorem                 |
| ---------------------------------------------------------- | ---------------------------- |
| Binary $\alpha$ ($0$ or $1$) degenerates $A_i$ to diagonal | `Theorems.BinaryAlpha`       |
| Regularization ensures invertibility                       | `Theorems.Invertibility`     |
| Shared matrix across R/G/B channels                        | `Theorems.ChannelReuse`      |
| Compositing error bounded by component errors              | `Theorems.CompositingError`  |
| Jacobi iteration contracts geometrically                   | `Theorems.JacobiContraction` |
| Clamp-free solution in $[0,1]$ when numerator bounds hold  | `Theorems.ClosedFormBox`     |

## 8. Evaluation Metrics

The paper reports three error measures over the translucent region
($\{i : 0 < \alpha_i^{\text{gt}} < 1\}$):

$$d_{\text{SAD}}(F^{\text{est}}, F^{\text{gt}}) = \sum_i \alpha_i^{\text{gt}} |F_i^{\text{est}} - F_i^{\text{gt}}|_1$$

$$d_{\text{MSE}}(F^{\text{est}}, F^{\text{gt}}) = \sum_i \alpha_i^{\text{gt}} |F_i^{\text{est}} - F_i^{\text{gt}}|_2^2$$

$$d_{\text{GRAD}}(F^{\text{est}}, F^{\text{gt}}) = \sum_i \alpha_i^{\text{gt}} |\nabla F_i^{\text{est}} - \nabla F_i^{\text{gt}}|_2^2$$

where $\nabla F$ is computed via first-order Gaussian derivative filters with $\sigma = 1.4$.

> **Lean:**
>
> - `Evaluation.ForegroundMetrics` defines `SAD`, `MSE`, and an abstract `GRAD` interface.
> - `Evaluation.DiscreteGrad` models the exact Python discrete kernel at $\sigma = 1.4$.
> - `Theorems.ForegroundMetrics` proves bounds and adversarial-family equalities.
> - `Theorems.DiscreteGrad` provides kernel positivity, normalization, and step-family
>   certificates.

## 9. Reported Results (Summary)

On the Rhemann et al. dataset (27 images), using ground-truth $\alpha$:

| Method                 | SAD ($\times 10^{-3}$) | MSE ($\times 10^3$) | GRAD ($\times 10^{-3}$) |
| ---------------------- | ---------------------: | ------------------: | ----------------------: |
| **Multi-Level (Ours)** |               **20.9** |                1.44 |                    8.89 |
| Closed-Form (Levin)    |                   21.1 |            **1.34** |                **8.13** |
| IndexNet (Lu)          |                   28.8 |                2.33 |                    11.1 |
| KNN (Chen)             |                   32.0 |                3.25 |                    16.1 |

Multi-Level runs >10x faster than the next-best method and uses <1/6 the memory.
With estimated (non-GT) alpha mattes, Multi-Level generally outperforms other methods
on SAD and GRAD.
