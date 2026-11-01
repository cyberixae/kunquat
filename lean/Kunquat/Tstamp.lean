/-
  A model of `src/lib/mathnum/Tstamp.c`.

  A timestamp is a pair of a whole number of beats and a remainder measured in
  units of 1 / KQT_TSTAMP_BEAT of a beat. The functions below follow the branch
  structure of the C code so that each C function can be compared with its model
  line by line. Fields are mathematical integers; the C machine-integer widths
  (int64_t beats, int32_t rem) are dealt with in the "Machine integers" section.
-/

namespace Kunquat

-- The model exists only to state and prove properties. Its definitions are
-- marked `noncomputable` so that none of it is compiled into the library
-- linked into C.

/-- `KQT_TSTAMP_BEAT` from `include/kunquat/limits.h`. -/
noncomputable def BEAT : Int := 882161280

structure Tstamp where
  beats : Int
  rem   : Int
  deriving DecidableEq

namespace Tstamp

/-- The condition checked by `Tstamp_validate` (and by `Tstamp_set`). -/
noncomputable def Valid (ts : Tstamp) : Prop := 0 ≤ ts.rem ∧ ts.rem < BEAT

/-- The exact time a timestamp denotes, in units of 1 / BEAT beats. -/
noncomputable def value (ts : Tstamp) : Int := ts.beats * BEAT + ts.rem

/-- `Tstamp_add` -/
noncomputable def add (ts1 ts2 : Tstamp) : Tstamp :=
  let beats := ts1.beats + ts2.beats
  let rem   := ts1.rem + ts2.rem
  if rem ≥ BEAT then ⟨beats + 1, rem - BEAT⟩
  else if rem < 0 then ⟨beats - 1, rem + BEAT⟩
  else ⟨beats, rem⟩

/-- `Tstamp_sub` -/
noncomputable def sub (ts1 ts2 : Tstamp) : Tstamp :=
  let beats := ts1.beats - ts2.beats
  let rem   := ts1.rem - ts2.rem
  if rem < 0 then ⟨beats - 1, rem + BEAT⟩
  else if rem ≥ BEAT then ⟨beats + 1, rem - BEAT⟩
  else ⟨beats, rem⟩

/-- `Tstamp_cmp` -/
noncomputable def cmp (ts1 ts2 : Tstamp) : Int :=
  if ts1.beats < ts2.beats then -1
  else if ts1.beats > ts2.beats then 1
  else if ts1.rem < ts2.rem then -1
  else if ts1.rem > ts2.rem then 1
  else 0

/-- `Tstamp_min` -/
noncomputable def min (ts1 ts2 : Tstamp) : Tstamp :=
  if cmp ts1 ts2 < 0 then ts1 else ts2

/-! ## The assertions in `Tstamp.c` never fail -/

/-- The `rassert`s at the end of `Tstamp_add` hold for all valid inputs. -/
theorem add_valid {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) : (add a b).Valid := by
  dsimp only [add]
  split <;> (try split) <;> simp only [Valid, BEAT] at * <;> (try dsimp only) <;> omega

/-- The `rassert`s at the end of `Tstamp_sub` hold for all valid inputs. -/
theorem sub_valid {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) : (sub a b).Valid := by
  dsimp only [sub]
  split <;> (try split) <;> simp only [Valid, BEAT] at * <;> (try dsimp only) <;> omega

/-- The second normalisation branch of `Tstamp_add` (`rem < 0`) is dead code
    for valid inputs. -/
theorem add_neg_branch_unreachable {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    ¬ (a.rem + b.rem < 0) := by
  simp only [Valid] at *; omega

/-- The second normalisation branch of `Tstamp_sub` (`rem ≥ BEAT`) is dead code
    for valid inputs. -/
theorem sub_overflow_branch_unreachable {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    ¬ (a.rem - b.rem ≥ BEAT) := by
  simp only [Valid] at *; omega

/-! ## Arithmetic is exact -/

theorem value_add (a b : Tstamp) : (add a b).value = a.value + b.value := by
  dsimp only [add]
  split <;> (try split) <;> simp only [value, BEAT] at * <;> omega

theorem value_sub (a b : Tstamp) : (sub a b).value = a.value - b.value := by
  dsimp only [sub]
  split <;> (try split) <;> simp only [value, BEAT] at * <;> omega

/-- A valid timestamp is the unique representation of its value. -/
theorem eq_of_value_eq {a b : Tstamp} (ha : a.Valid) (hb : b.Valid)
    (h : a.value = b.value) : a = b := by
  simp only [Valid, value, BEAT] at *
  have hb' : a.beats = b.beats := by omega
  have hr : a.rem = b.rem := by omega
  cases a; cases b; simp_all

/-! ## Comparison agrees with the values -/

theorem cmp_lt_iff {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    cmp a b < 0 ↔ a.value < b.value := by
  simp only [Valid, value, BEAT] at *
  unfold cmp
  repeat' split
  all_goals omega

theorem cmp_eq_zero_iff {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    cmp a b = 0 ↔ a = b := by
  constructor
  · intro h
    have hv : a.value = b.value := by
      simp only [Valid, value, BEAT] at *
      unfold cmp at h
      repeat' split at h
      all_goals omega
    exact eq_of_value_eq ha hb hv
  · intro h; subst h; unfold cmp; simp

theorem cmp_gt_iff {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    cmp a b > 0 ↔ a.value > b.value := by
  simp only [Valid, value, BEAT] at *
  unfold cmp
  repeat' split
  all_goals omega

/-- `Tstamp_min` returns the earlier timestamp. -/
theorem value_min {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    (min a b).value = if a.value ≤ b.value then a.value else b.value := by
  unfold min
  split
  · next h => rw [cmp_lt_iff ha hb] at h; simp only [Int.le_of_lt h, ite_true]
  · next h =>
    rw [cmp_lt_iff ha hb] at h
    by_cases hle : a.value ≤ b.value
    · simp only [hle, ite_true]
      exact congrArg value (eq_of_value_eq hb ha (by omega))
    · simp only [hle, ite_false]

/-! ## Example: slide end times

  The specification says a tempo slide of length 3 that begins at row
  timestamp 2 always finishes at timestamp 5.
-/

example : add ⟨2, 0⟩ ⟨3, 0⟩ = ⟨5, 0⟩ := by decide

/-- For any start and length, `start + length - length = start` exactly,
    so slide end points never drift. -/
theorem sub_add_cancel {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    sub (add a b) b = a := by
  apply eq_of_value_eq (sub_valid (add_valid ha hb) hb) ha
  rw [value_sub, value_add]; omega

/-! ## Machine integers

  `rem` is an `int32_t`. The intermediate sums `ts1->rem + ts2->rem` and
  `ts1->rem - ts2->rem` are computed in `int32_t` before normalisation, so the
  C code is only correct if they cannot overflow. They can't: -/

noncomputable def INT32_MIN : Int := -2147483648
noncomputable def INT32_MAX : Int := 2147483647

theorem add_rem_no_int32_overflow {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    INT32_MIN ≤ a.rem + b.rem ∧ a.rem + b.rem ≤ INT32_MAX := by
  simp only [Valid, BEAT, INT32_MIN, INT32_MAX] at *; omega

theorem sub_rem_no_int32_overflow {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    INT32_MIN ≤ a.rem - b.rem ∧ a.rem - b.rem ≤ INT32_MAX := by
  simp only [Valid, BEAT, INT32_MIN, INT32_MAX] at *; omega

/-! `beats` is an `int64_t`, and `Tstamp_add` / `Tstamp_sub` do not check it.
  The carry is at most one beat, so overflow happens exactly when the true
  result falls outside the `int64_t` range. Callers must rule that out. -/

noncomputable def INT64_MIN : Int := -9223372036854775808
noncomputable def INT64_MAX : Int := 9223372036854775807

theorem add_beats_carry {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    (add a b).beats = a.beats + b.beats ∨ (add a b).beats = a.beats + b.beats + 1 := by
  have hv := value_add a b
  have hr := add_valid ha hb
  simp only [Valid, value, BEAT] at *
  omega

theorem sub_beats_borrow {a b : Tstamp} (ha : a.Valid) (hb : b.Valid) :
    (sub a b).beats = a.beats - b.beats ∨ (sub a b).beats = a.beats - b.beats - 1 := by
  have hv := value_sub a b
  have hr := sub_valid ha hb
  simp only [Valid, value, BEAT] at *
  omega

end Tstamp
end Kunquat
