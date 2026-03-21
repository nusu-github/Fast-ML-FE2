import FastMLFE2.Notation

namespace FastMLFE2

/-- Neighbor data for a single local optimization problem. -/
structure LocalData (ι : Type*) where
  weights : ι → ℝ
  fgNeighbors : ι → ℝ
  bgNeighbors : ι → ℝ

namespace LocalData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev BlockIdx (ι : Type*) := Sum ι ι

def totalWeight (data : LocalData ι) : ℝ :=
  ∑ j, data.weights j

def foregroundSum (data : LocalData ι) : ℝ :=
  ∑ j, data.weights j * data.fgNeighbors j

def backgroundSum (data : LocalData ι) : ℝ :=
  ∑ j, data.weights j * data.bgNeighbors j

def weightVec (data : LocalData ι) : BlockIdx ι → ℝ
  | Sum.inl j => data.weights j
  | Sum.inr j => data.weights j

def neighborVec (data : LocalData ι) : BlockIdx ι → ℝ
  | Sum.inl j => data.fgNeighbors j
  | Sum.inr j => data.bgNeighbors j

/-- The matrix `R` from the paper, duplicated over `Sum ι ι` indices. -/
def broadcastMatrix : Matrix (BlockIdx ι) FBIdx ℝ
  | Sum.inl _ => ![1, 0]
  | Sum.inr _ => ![0, 1]

/-- The block-diagonal matrix `V`, represented as a diagonal matrix on `Sum ι ι`. -/
def weightMatrix (data : LocalData ι) : Matrix (BlockIdx ι) (BlockIdx ι) ℝ :=
  Matrix.diagonal (data.weightVec)

def neighborResidual (data : LocalData ι) (g : FBVec) : BlockIdx ι → ℝ :=
  (broadcastMatrix (ι := ι)).mulVec g - data.neighborVec

/-- The reduced `2 × 2` system matrix `U Uᵀ + Rᵀ V R`. -/
def systemMatrix (data : LocalData ι) (α : ℝ) : Matrix FBIdx FBIdx ℝ :=
  ![![α ^ 2 + data.totalWeight, α * (1 - α)],
    ![α * (1 - α), (1 - α) ^ 2 + data.totalWeight]]

/-- The rank-one matrix `U Uᵀ` from the paper. -/
def compositingMatrix (α : ℝ) : Matrix FBIdx FBIdx ℝ :=
  fun i j => uVec α i * uVec α j

/-- The unreduced paper matrix `U Uᵀ + Rᵀ V R`. -/
def paperSystemMatrix (data : LocalData ι) (α : ℝ) : Matrix FBIdx FBIdx ℝ :=
  compositingMatrix α +
    ((broadcastMatrix (ι := ι)).transpose * data.weightMatrix * broadcastMatrix)

/-- The reduced right-hand side `I U + Rᵀ V h`. -/
def rhs (data : LocalData ι) (α image : ℝ) : FBVec :=
  ![
    α * image + data.foregroundSum,
    (1 - α) * image + data.backgroundSum
  ]

/-- The unreduced paper right-hand side `I U + Rᵀ V h`. -/
def paperRhs (data : LocalData ι) (α image : ℝ) : FBVec :=
  image • uVec α +
    (((broadcastMatrix (ι := ι)).transpose * data.weightMatrix).mulVec data.neighborVec)

def localSystem (data : LocalData ι) (α image : ℝ) (g : FBVec) : Prop :=
  (data.systemMatrix α).mulVec g = data.rhs α image

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem weightVec_inl (data : LocalData ι) (j : ι) :
    data.weightVec (Sum.inl j) = data.weights j := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem weightVec_inr (data : LocalData ι) (j : ι) :
    data.weightVec (Sum.inr j) = data.weights j := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem neighborVec_inl (data : LocalData ι) (j : ι) :
    data.neighborVec (Sum.inl j) = data.fgNeighbors j := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem neighborVec_inr (data : LocalData ι) (j : ι) :
    data.neighborVec (Sum.inr j) = data.bgNeighbors j := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem broadcastMatrix_mulVec_inl (g : FBVec) (j : ι) :
    (broadcastMatrix (ι := ι)).mulVec g (Sum.inl j) = foreground g := by
  simp [broadcastMatrix, foreground, Matrix.mulVec]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem broadcastMatrix_mulVec_inr (g : FBVec) (j : ι) :
    (broadcastMatrix (ι := ι)).mulVec g (Sum.inr j) = background g := by
  simp [broadcastMatrix, background, Matrix.mulVec]

@[simp] theorem weightMatrix_mulVec_apply (data : LocalData ι)
    (x : BlockIdx ι → ℝ) (idx : BlockIdx ι) :
    data.weightMatrix.mulVec x idx = data.weightVec idx * x idx := by
  simp [weightMatrix, Matrix.mulVec]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem neighborResidual_inl (data : LocalData ι) (g : FBVec) (j : ι) :
    data.neighborResidual g (Sum.inl j) = foreground g - data.fgNeighbors j := by
  simp [neighborResidual, foreground]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem neighborResidual_inr (data : LocalData ι) (g : FBVec) (j : ι) :
    data.neighborResidual g (Sum.inr j) = background g - data.bgNeighbors j := by
  simp [neighborResidual, background]

omit [DecidableEq ι] in
@[simp] theorem systemMatrix_mulVec_foreground (data : LocalData ι) (α : ℝ) (g : FBVec) :
    (data.systemMatrix α).mulVec g 0 =
      (α ^ 2 + data.totalWeight) * foreground g + α * (1 - α) * background g := by
  simp [systemMatrix, foreground, background, Matrix.mulVec]

omit [DecidableEq ι] in
@[simp] theorem systemMatrix_mulVec_background (data : LocalData ι) (α : ℝ) (g : FBVec) :
    (data.systemMatrix α).mulVec g 1 =
      α * (1 - α) * foreground g + ((1 - α) ^ 2 + data.totalWeight) * background g := by
  simp [systemMatrix, foreground, background, Matrix.mulVec]

omit [DecidableEq ι] in
@[simp] theorem rhs_foreground (data : LocalData ι) (α image : ℝ) :
    foreground (data.rhs α image) = α * image + data.foregroundSum := by
  simp [rhs, foreground]

omit [DecidableEq ι] in
@[simp] theorem rhs_background (data : LocalData ι) (α image : ℝ) :
    background (data.rhs α image) = (1 - α) * image + data.backgroundSum := by
  simp [rhs, background]

@[simp] theorem compositingMatrix_apply (α : ℝ) (i j : FBIdx) :
    compositingMatrix α i j = uVec α i * uVec α j := rfl

@[simp] theorem weightedBroadcastMatrix_apply_00 (data : LocalData ι) :
    ((((broadcastMatrix (ι := ι)).transpose * data.weightMatrix *
        (broadcastMatrix (ι := ι))) 0) 0) =
      data.totalWeight := by
  simp [broadcastMatrix, weightMatrix, totalWeight, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.diagonal, Fintype.sum_sum_type]

@[simp] theorem weightedBroadcastMatrix_apply_01 (data : LocalData ι) :
    ((((broadcastMatrix (ι := ι)).transpose * data.weightMatrix *
        (broadcastMatrix (ι := ι))) 0) 1) = 0 := by
  simp [broadcastMatrix, weightMatrix, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.diagonal, Fintype.sum_sum_type]

@[simp] theorem weightedBroadcastMatrix_apply_10 (data : LocalData ι) :
    ((((broadcastMatrix (ι := ι)).transpose * data.weightMatrix *
        (broadcastMatrix (ι := ι))) 1) 0) = 0 := by
  simp [broadcastMatrix, weightMatrix, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.diagonal, Fintype.sum_sum_type]

@[simp] theorem weightedBroadcastMatrix_apply_11 (data : LocalData ι) :
    ((((broadcastMatrix (ι := ι)).transpose * data.weightMatrix *
        (broadcastMatrix (ι := ι))) 1) 1) =
      data.totalWeight := by
  simp [broadcastMatrix, weightMatrix, totalWeight, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.diagonal, Fintype.sum_sum_type]

@[simp] theorem weightedBroadcastRhs_foreground (data : LocalData ι) :
    ((((broadcastMatrix (ι := ι)).transpose * data.weightMatrix).mulVec data.neighborVec) 0) =
      data.foregroundSum := by
  simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, broadcastMatrix, weightMatrix,
    neighborVec, weightVec, foregroundSum, Matrix.transpose_apply, Matrix.diagonal,
    Fintype.sum_sum_type]

@[simp] theorem weightedBroadcastRhs_background (data : LocalData ι) :
    ((((broadcastMatrix (ι := ι)).transpose * data.weightMatrix).mulVec data.neighborVec) 1) =
      data.backgroundSum := by
  simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, broadcastMatrix, weightMatrix,
    neighborVec, weightVec, backgroundSum, Matrix.transpose_apply, Matrix.diagonal,
    Fintype.sum_sum_type]

@[simp] theorem paperSystemMatrix_eq_systemMatrix (data : LocalData ι) (α : ℝ) :
    data.paperSystemMatrix α = data.systemMatrix α := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [paperSystemMatrix, systemMatrix, compositingMatrix, uVec, pow_two,
      weightedBroadcastMatrix_apply_00]
  · simp [paperSystemMatrix, systemMatrix, compositingMatrix, uVec,
      weightedBroadcastMatrix_apply_01]
  · simp [paperSystemMatrix, systemMatrix, compositingMatrix, uVec,
      weightedBroadcastMatrix_apply_10]
    ring
  · simp [paperSystemMatrix, systemMatrix, compositingMatrix, uVec, pow_two,
      weightedBroadcastMatrix_apply_11]

@[simp] theorem paperRhs_eq_rhs (data : LocalData ι) (α image : ℝ) :
    data.paperRhs α image = data.rhs α image := by
  ext i; fin_cases i
  all_goals
    ring_nf
    simp [paperRhs, rhs, uVec]
    ring

end LocalData

end FastMLFE2
