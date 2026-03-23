import FastMLFE2.Theory.Canonical.Grid

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Canonical

namespace GridPixelData

theorem canonicalNeighborhood_eq_fourNeighborhood
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w) :
    data.toCanonicalPixelData.canonicalNeighborhood p = fourNeighborhood p := by
  rfl

end GridPixelData

theorem neighborPixel_mem_fourNeighborhood
    {h w : Nat}
    (p : Pixel h w)
    (j : ValidDir p) :
    neighborPixel p j ∈ fourNeighborhood p := by
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

private theorem validDirections_card_eq_validDirCount
    {h w : Nat}
    (p : Pixel h w) :
    (validDirections p).card = validDirCount p := by
  by_cases hUp : IsValidDir p .up
  · by_cases hDown : IsValidDir p .down
    · by_cases hLeft : IsValidDir p .left
      · by_cases hRight : IsValidDir p .right
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
      · by_cases hRight : IsValidDir p .right
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
    · by_cases hLeft : IsValidDir p .left
      · by_cases hRight : IsValidDir p .right
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
      · by_cases hRight : IsValidDir p .right
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
  · by_cases hDown : IsValidDir p .down
    · by_cases hLeft : IsValidDir p .left
      · by_cases hRight : IsValidDir p .right
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
      · by_cases hRight : IsValidDir p .right
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
    · by_cases hLeft : IsValidDir p .left
      · by_cases hRight : IsValidDir p .right
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
      · by_cases hRight : IsValidDir p .right
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]
        · simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]

theorem card_validDir_eq_validDirCount
    {h w : Nat}
    (p : Pixel h w) :
    Fintype.card (ValidDir p) = validDirCount p := by
  classical
  change Fintype.card { x // IsValidDir p x } = validDirCount p
  have hmem : ∀ d : Direction4, d ∈ validDirections p ↔ IsValidDir p d := by
    intro d
    cases d <;> constructor <;> intro h <;> simp [validDirections, IsValidDir] at h ⊢ <;> aesop
  have hcard : Fintype.card { x // IsValidDir p x } = (validDirections p).card :=
    Fintype.card_of_subtype (validDirections p) hmem
  calc
    Fintype.card { x // IsValidDir p x } = (validDirections p).card := hcard
    _ = validDirCount p := validDirections_card_eq_validDirCount p

theorem card_validDir_eq_four_of_isInterior
    {h w : Nat}
    (p : Pixel h w)
    (hInterior : IsInterior p) :
    Fintype.card (ValidDir p) = 4 := by
  rcases hInterior with ⟨hUp, hDown, hLeft, hRight⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hUp, hDown, hLeft, hRight]

theorem card_validDir_eq_three_of_isTopEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hTop : IsTopEdgeNoncorner p) :
    Fintype.card (ValidDir p) = 3 := by
  rcases (show p.1.1 = 0 ∧ p.1.1 + 1 < h ∧ 0 < p.2.1 ∧ p.2.1 + 1 < w from
    by simpa [IsTopEdgeNoncorner] using hTop) with ⟨hRow, hDown, hLeft, hRight⟩
  have hDown' : 1 < h := by
    simpa [hRow] using hDown
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hRow, hDown', hLeft, hRight]

theorem card_validDir_eq_three_of_isBottomEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hBottom : IsBottomEdgeNoncorner p) :
    Fintype.card (ValidDir p) = 3 := by
  rcases (show 0 < p.1.1 ∧ p.1.1 + 1 = h ∧ 0 < p.2.1 ∧ p.2.1 + 1 < w from
    by simpa [IsBottomEdgeNoncorner] using hBottom) with ⟨hUp, hRow, hLeft, hRight⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hUp, hRow, hLeft, hRight]

theorem card_validDir_eq_three_of_isLeftEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hLeft : IsLeftEdgeNoncorner p) :
    Fintype.card (ValidDir p) = 3 := by
  rcases (show 0 < p.1.1 ∧ p.1.1 + 1 < h ∧ p.2.1 = 0 ∧ p.2.1 + 1 < w from
    by simpa [IsLeftEdgeNoncorner] using hLeft) with ⟨hUp, hDown, hCol, hRight⟩
  have hWidth : 1 < w := by
    simpa [hCol] using hRight
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hUp, hDown, hCol, hWidth]

theorem card_validDir_eq_three_of_isRightEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hRight : IsRightEdgeNoncorner p) :
    Fintype.card (ValidDir p) = 3 := by
  rcases (show 0 < p.1.1 ∧ p.1.1 + 1 < h ∧ 0 < p.2.1 ∧ p.2.1 + 1 = w from
    by simpa [IsRightEdgeNoncorner] using hRight) with ⟨hUp, hDown, hLeft, hCol⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hUp, hDown, hLeft, hCol]

theorem card_validDir_eq_two_of_isTopLeftCorner
    {h w : Nat}
    [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w)
    (hCorner : IsTopLeftCorner p) :
    Fintype.card (ValidDir p) = 2 := by
  rcases (show p.1.1 = 0 ∧ p.2.1 = 0 from by simpa [IsTopLeftCorner] using hCorner) with
    ⟨hTop, hLeftEq⟩
  have hHeight : 1 < h := by
    have hh : 2 ≤ h := Fact.out
    omega
  have hWidth : 1 < w := by
    have hw : 2 ≤ w := Fact.out
    omega
  have hDown : IsValidDir p .down := by
    simpa [IsValidDir, hTop] using hHeight
  have hRight : IsValidDir p .right := by
    simpa [IsValidDir, hLeftEq] using hWidth
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hTop, hLeftEq, hHeight, hWidth]

theorem card_validDir_eq_two_of_isTopRightCorner
    {h w : Nat}
    [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w)
    (hCorner : IsTopRightCorner p) :
    Fintype.card (ValidDir p) = 2 := by
  rcases (show p.1.1 = 0 ∧ p.2.1 + 1 = w from by simpa [IsTopRightCorner] using hCorner) with
    ⟨hTop, hRightEq⟩
  have hHeight : 1 < h := by
    have hh : 2 ≤ h := Fact.out
    omega
  have hLeftVal : 0 < p.2.1 := by
    have hw : 2 ≤ w := Fact.out
    omega
  have hDown : IsValidDir p .down := by
    simpa [IsValidDir, hTop] using hHeight
  have hLeft : IsValidDir p .left := by
    simpa [IsValidDir] using hLeftVal
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hTop, hRightEq, hHeight, hLeftVal]

theorem card_validDir_eq_two_of_isBottomLeftCorner
    {h w : Nat}
    [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w)
    (hCorner : IsBottomLeftCorner p) :
    Fintype.card (ValidDir p) = 2 := by
  rcases (show p.1.1 + 1 = h ∧ p.2.1 = 0 from by simpa [IsBottomLeftCorner] using hCorner) with
    ⟨hBottomEq, hLeftEq⟩
  have hUpVal : 0 < p.1.1 := by
    have hh : 2 ≤ h := Fact.out
    omega
  have hWidth : 1 < w := by
    have hw : 2 ≤ w := Fact.out
    omega
  have hUp : IsValidDir p .up := by
    simpa [IsValidDir] using hUpVal
  have hRight : IsValidDir p .right := by
    simpa [IsValidDir, hLeftEq] using hWidth
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hBottomEq, hLeftEq, hUpVal, hWidth]

theorem card_validDir_eq_two_of_isBottomRightCorner
    {h w : Nat}
    [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w)
    (hCorner : IsBottomRightCorner p) :
    Fintype.card (ValidDir p) = 2 := by
  rcases (show p.1.1 + 1 = h ∧ p.2.1 + 1 = w from by simpa [IsBottomRightCorner] using hCorner) with
    ⟨hBottomEq, hRightEq⟩
  have hUpVal : 0 < p.1.1 := by
    have hh : 2 ≤ h := Fact.out
    omega
  have hLeftVal : 0 < p.2.1 := by
    have hw : 2 ≤ w := Fact.out
    omega
  have hUp : IsValidDir p .up := by
    simpa [IsValidDir] using hUpVal
  have hLeft : IsValidDir p .left := by
    simpa [IsValidDir] using hLeftVal
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hBottomEq, hRightEq, hUpVal, hLeftVal]

end FastMLFE2.Theory.Theorems
