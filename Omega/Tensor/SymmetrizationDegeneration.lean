module

public import Omega.Tensor.Symmetrization
public import Omega.Tensor.DegenerationOperations

/-!
# Factor permutations and symmetrization preserve degeneration

Permute the three polynomial factor maps in the same way as the tensor
factors. Products of these witnesses then give the six-factor symmetrization.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplication.Tensor

variable {R I J L I' J' L' : Type*}

/-- Rotating the factors rotates their factor maps. -/
theorem map_rotate [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T : Tensor R I J L) :
    map B C A (rotate T) = rotate (map A B C T) := by
  funext j k i
  simp only [map, rotate]
  calc
    _ = ∑ b, ∑ a, ∑ c, B j b * C k c * A i a * T a b c := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ c, B j b * C k c * A i a * T a b c := Finset.sum_comm
    _ = _ := by simp only [mul_comm, mul_left_comm]

/-- Swapping the first two factors swaps their factor maps. -/
theorem map_swapFirstTwo [CommSemiring R] [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I R) (B : Matrix J' J R) (C : Matrix L' L R)
    (T : Tensor R I J L) :
    map B A C (swapFirstTwo T) = swapFirstTwo (map A B C T) := by
  funext j i k
  simp only [map, swapFirstTwo]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Rotate the maps in a polynomial degeneration witness. -/
def DegenerationWitness.rotate [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (w : DegenerationWitness T S) :
    DegenerationWitness (Tensor.rotate T) (Tensor.rotate S) where
  order := w.order
  firstMap := w.secondMap
  secondMap := w.thirdMap
  thirdMap := w.firstMap
  remainder := Tensor.rotate w.remainder
  equation := by
    intro j k i
    change map w.secondMap w.thirdMap w.firstMap (Tensor.rotate (liftPolynomial T)) j k i = _
    rw [map_rotate]
    exact w.equation i j k

/-- Swap the first two maps in a polynomial degeneration witness. -/
def DegenerationWitness.swapFirstTwo [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (w : DegenerationWitness T S) :
    DegenerationWitness (Tensor.swapFirstTwo T) (Tensor.swapFirstTwo S) where
  order := w.order
  firstMap := w.secondMap
  secondMap := w.firstMap
  thirdMap := w.thirdMap
  remainder := Tensor.swapFirstTwo w.remainder
  equation := by
    intro j i k
    change map w.secondMap w.firstMap w.thirdMap
      (Tensor.swapFirstTwo (liftPolynomial T)) j i k = _
    rw [map_swapFirstTwo]
    exact w.equation i j k

theorem Degenerates.rotate [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Degenerates T S) :
    Degenerates (Tensor.rotate T) (Tensor.rotate S) := by
  obtain ⟨w⟩ := h
  exact ⟨w.rotate⟩

theorem Degenerates.swapFirstTwo [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Degenerates T S) :
    Degenerates (Tensor.swapFirstTwo T) (Tensor.swapFirstTwo S) := by
  obtain ⟨w⟩ := h
  exact ⟨w.swapFirstTwo⟩

/-- The cyclic product preserves degeneration. -/
theorem Degenerates.cyclicSymmetrize [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Degenerates T S) :
    Degenerates (Tensor.cyclicSymmetrize T) (Tensor.cyclicSymmetrize S) :=
  h.kronecker (h.rotate.kronecker h.rotate.rotate)

/-- Full symmetrization preserves degeneration. -/
theorem Degenerates.symmetrize [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor R I J L} {S : Tensor R I' J' L'} (h : Degenerates T S) :
    Degenerates (Tensor.symmetrize T) (Tensor.symmetrize S) :=
  h.cyclicSymmetrize.kronecker h.swapFirstTwo.cyclicSymmetrize

@[simp]
theorem symmetrize_zero [MulZeroClass R] :
    symmetrize (0 : Tensor R I J L) = 0 := by
  funext i j k
  simp [symmetrize, cyclicSymmetrize, kronecker, rotate, swapFirstTwo]

@[simp]
theorem kronecker_zero_right [MulZeroClass R] (T : Tensor R I J L) :
    kronecker T (0 : Tensor R I' J' L') = 0 := by
  funext i j k
  exact mul_zero _

@[simp]
theorem kronecker_zero_left [MulZeroClass R] (T : Tensor R I J L) :
    kronecker (0 : Tensor R I' J' L') T = 0 := by
  funext i j k
  exact zero_mul _

/-- Every positive power of the zero tensor is zero. -/
theorem kroneckerPower_zero_of_pos [CommMonoidWithZero R] (n : ℕ) (hn : 0 < n) :
    kroneckerPower (0 : Tensor R I J L) n = 0 := by
  funext i j k
  simp [kroneckerPower, Nat.ne_of_gt hn]

end MatrixMultiplication.Tensor
