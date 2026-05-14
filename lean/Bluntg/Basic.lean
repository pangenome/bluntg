/-
Basic helpers: prefix/suffix/middle of a List.

We work with `List α` as our sequence type. Three primitive operations on a
sequence `s : List α`:

  • `prefix s n`   first `n` symbols of `s` (clamped to `s.length`)
  • `suffix s n`   last `n` symbols of `s` (clamped to `s.length`)
  • `middle s l r` drop `l` from the front and `r` from the back

We define them in terms of `List.take`/`List.drop` and prove the small
combinatorial lemmas the rest of the development needs.
-/

namespace Bluntg

variable {α : Type _}

/-- First `n` symbols of `s` (clamped to `s.length`). -/
def Prefix (s : List α) (n : Nat) : List α := s.take n

/-- Last `n` symbols of `s` (clamped to `s.length`). -/
def Suffix (s : List α) (n : Nat) : List α := s.drop (s.length - n)

/-- Drop `l` symbols from the front and `r` symbols from the back.
    If `l + r ≥ s.length`, returns `[]`. -/
def middle (s : List α) (l r : Nat) : List α :=
  (s.drop l).take (s.length - l - r)

@[simp] theorem prefix_zero (s : List α) : Prefix s 0 = [] := rfl

@[simp] theorem suffix_zero (s : List α) : Suffix s 0 = [] := by
  simp [Suffix]

@[simp] theorem middle_zero_zero (s : List α) : middle s 0 0 = s := by
  simp [middle]

theorem length_prefix (s : List α) (n : Nat) :
    (Prefix s n).length = min n s.length := by
  simp [Prefix, List.length_take]

theorem length_suffix (s : List α) (n : Nat) :
    (Suffix s n).length = min n s.length := by
  simp [Suffix, List.length_drop]
  omega

theorem length_middle (s : List α) (l r : Nat) :
    (middle s l r).length = min (s.length - l - r) (s.length - l) := by
  simp [middle, List.length_take, List.length_drop]

/-- `prefix s n ++ drop n s = s`. Useful for splitting walks at a prefix. -/
theorem prefix_append_drop (s : List α) (n : Nat) :
    Prefix s n ++ s.drop n = s := by
  simp [Prefix]

/-- `take (length - n) ++ suffix n = s`. Dual of `prefix_append_drop`. -/
theorem take_append_suffix (s : List α) (n : Nat) :
    s.take (s.length - n) ++ Suffix s n = s := by
  simp [Suffix, List.take_append_drop]

/-- Sandwich identity used by path-preservation: a sequence equals
    `prefix l ++ middle l r ++ suffix r` whenever the trims fit. -/
theorem prefix_middle_suffix (s : List α) (l r : Nat)
    (h : l + r ≤ s.length) :
    Prefix s l ++ middle s l r ++ Suffix s r = s := by
  simp only [Prefix, middle, Suffix]
  -- After unfolding the goal is:
  --   s.take l ++ (s.drop l).take (s.length - l - r) ++ s.drop (s.length - r) = s
  -- Express `s.drop (s.length - r)` as the back half of `s.drop l` cut at
  -- position `s.length - l - r`.
  have key : (s.drop l).drop (s.length - l - r) = s.drop (s.length - r) := by
    rw [List.drop_drop]
    congr 1
    omega
  calc s.take l ++ (s.drop l).take (s.length - l - r) ++ s.drop (s.length - r)
      = s.take l ++ ((s.drop l).take (s.length - l - r) ++ s.drop (s.length - r)) := by
          rw [List.append_assoc]
    _ = s.take l
          ++ ((s.drop l).take (s.length - l - r)
               ++ (s.drop l).drop (s.length - l - r)) := by rw [key]
    _ = s.take l ++ s.drop l := by rw [List.take_append_drop]
    _ = s := List.take_append_drop _ _

/-- Overlap-merge identity: if the last `w` chars of `A` equal the first
    `w` chars of `B`, then `A ++ B.drop w = A.take (|A| - w) ++ B`. -/
theorem append_drop_eq_take_append {β : Type _} (A B : List β) (w : Nat)
    (h_overlap : A.drop (A.length - w) = B.take w) :
    A ++ B.drop w = A.take (A.length - w) ++ B := by
  calc A ++ B.drop w
      = (A.take (A.length - w) ++ A.drop (A.length - w)) ++ B.drop w := by
          rw [List.take_append_drop]
    _ = A.take (A.length - w) ++ (A.drop (A.length - w) ++ B.drop w) := by
          rw [List.append_assoc]
    _ = A.take (A.length - w) ++ (B.take w ++ B.drop w) := by
          rw [h_overlap]
    _ = A.take (A.length - w) ++ B := by
          rw [List.take_append_drop]

end Bluntg
