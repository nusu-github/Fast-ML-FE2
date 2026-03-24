import FastMLFE2.Canonical.Grid

namespace FastMLFE2.Theorems

open FastMLFE2.Canonical

namespace GridPixelData

theorem canonicalNeighborhood_eq_fourNeighborhood
    {h w : Nat} (data : GridPixelData h w) (p : Pixel h w) :
    data.toCanonicalPixelData.canonicalNeighborhood p = fourNeighborhood p := rfl

end GridPixelData

theorem neighborPixel_mem_fourNeighborhood
    {h w : Nat} (p : Pixel h w) (j : ValidDir p) :
    neighborPixel p j ∈ fourNeighborhood p :=
  Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

private theorem validDirections_card_eq_validDirCount
    {h w : Nat} (p : Pixel h w) :
    (validDirections p).card = validDirCount p := by
  by_cases hUp : IsValidDir p .up <;>
    by_cases hDown : IsValidDir p .down <;>
      by_cases hLeft : IsValidDir p .left <;>
        by_cases hRight : IsValidDir p .right <;>
          simp [validDirections, validDirCount, hUp, hDown, hLeft, hRight]

theorem card_validDir_eq_validDirCount
    {h w : Nat} (p : Pixel h w) :
    Fintype.card (ValidDir p) = validDirCount p := by
  classical
  have hmem : ∀ d : Direction4, d ∈ validDirections p ↔ IsValidDir p d :=
    fun d => by cases d <;> constructor <;> intro h <;>
      simp [validDirections, IsValidDir] at h ⊢ <;> aesop
  rw [Fintype.card_of_subtype (validDirections p) hmem,
    validDirections_card_eq_validDirCount]

theorem card_validDir_eq_four_of_isInterior
    {h w : Nat} (p : Pixel h w) (hInterior : IsInterior p) :
    Fintype.card (ValidDir p) = 4 := by
  rcases hInterior with ⟨hUp, hDown, hLeft, hRight⟩
  rw [card_validDir_eq_validDirCount]; simp [validDirCount, IsValidDir, *]

theorem card_validDir_eq_three_of_isTopEdgeNoncorner
    {h w : Nat} (p : Pixel h w) (hTop : IsTopEdgeNoncorner p) :
    Fintype.card (ValidDir p) = 3 := by
  rcases (show p.1.1 = 0 ∧ p.1.1 + 1 < h ∧ 0 < p.2.1 ∧ p.2.1 + 1 < w from
    by simpa [IsTopEdgeNoncorner] using hTop) with ⟨hRow, hDown, hLeft, hRight⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hRow, show 1 < h from by omega, hLeft, hRight]

theorem card_validDir_eq_three_of_isBottomEdgeNoncorner
    {h w : Nat} (p : Pixel h w) (hBottom : IsBottomEdgeNoncorner p) :
    Fintype.card (ValidDir p) = 3 := by
  rcases (show 0 < p.1.1 ∧ p.1.1 + 1 = h ∧ 0 < p.2.1 ∧ p.2.1 + 1 < w from
    by simpa [IsBottomEdgeNoncorner] using hBottom) with ⟨hUp, hRow, hLeft, hRight⟩
  rw [card_validDir_eq_validDirCount]; simp [validDirCount, IsValidDir, hUp, hRow, hLeft, hRight]

theorem card_validDir_eq_three_of_isLeftEdgeNoncorner
    {h w : Nat} (p : Pixel h w) (hLeft : IsLeftEdgeNoncorner p) :
    Fintype.card (ValidDir p) = 3 := by
  rcases (show 0 < p.1.1 ∧ p.1.1 + 1 < h ∧ p.2.1 = 0 ∧ p.2.1 + 1 < w from
    by simpa [IsLeftEdgeNoncorner] using hLeft) with ⟨hUp, hDown, hCol, hRight⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hUp, hDown, hCol, show 1 < w from by omega]

theorem card_validDir_eq_three_of_isRightEdgeNoncorner
    {h w : Nat} (p : Pixel h w) (hRight : IsRightEdgeNoncorner p) :
    Fintype.card (ValidDir p) = 3 := by
  rcases (show 0 < p.1.1 ∧ p.1.1 + 1 < h ∧ 0 < p.2.1 ∧ p.2.1 + 1 = w from
    by simpa [IsRightEdgeNoncorner] using hRight) with ⟨hUp, hDown, hLeft, hCol⟩
  rw [card_validDir_eq_validDirCount]; simp [validDirCount, IsValidDir, hUp, hDown, hLeft, hCol]

theorem card_validDir_eq_two_of_isTopLeftCorner
    {h w : Nat} [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w) (hCorner : IsTopLeftCorner p) :
    Fintype.card (ValidDir p) = 2 := by
  rcases (show p.1.1 = 0 ∧ p.2.1 = 0 from by simpa [IsTopLeftCorner] using hCorner) with ⟨hT, hL⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hT, hL, show 1 < h from by have := Fact.out (p := 2 ≤ h); omega,
    show 1 < w from by have := Fact.out (p := 2 ≤ w); omega]

theorem card_validDir_eq_two_of_isTopRightCorner
    {h w : Nat} [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w) (hCorner : IsTopRightCorner p) :
    Fintype.card (ValidDir p) = 2 := by
  rcases
      (show p.1.1 = 0 ∧ p.2.1 + 1 = w from
        by simpa [IsTopRightCorner] using hCorner)
    with ⟨hT, hR⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hT, hR, show 1 < h from by have := Fact.out (p := 2 ≤ h); omega,
    show 0 < p.2.1 from by have := Fact.out (p := 2 ≤ w); omega]

theorem card_validDir_eq_two_of_isBottomLeftCorner
    {h w : Nat} [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w) (hCorner : IsBottomLeftCorner p) :
    Fintype.card (ValidDir p) = 2 := by
  rcases
      (show p.1.1 + 1 = h ∧ p.2.1 = 0 from
        by simpa [IsBottomLeftCorner] using hCorner)
    with ⟨hB, hL⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hB, hL,
    show 0 < p.1.1 from by have := Fact.out (p := 2 ≤ h); omega,
    show 1 < w from by have := Fact.out (p := 2 ≤ w); omega]

theorem card_validDir_eq_two_of_isBottomRightCorner
    {h w : Nat} [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w) (hCorner : IsBottomRightCorner p) :
    Fintype.card (ValidDir p) = 2 := by
  rcases
      (show p.1.1 + 1 = h ∧ p.2.1 + 1 = w from
        by simpa [IsBottomRightCorner] using hCorner)
    with ⟨hB, hR⟩
  rw [card_validDir_eq_validDirCount]
  simp [validDirCount, IsValidDir, hB, hR,
    show 0 < p.1.1 from by have := Fact.out (p := 2 ≤ h); omega,
    show 0 < p.2.1 from by have := Fact.out (p := 2 ≤ w); omega]

end FastMLFE2.Theorems
