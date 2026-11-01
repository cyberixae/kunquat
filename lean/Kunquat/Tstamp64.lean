import Kunquat.Tstamp

/-
  A fixed-width implementation of `src/lib/mathnum/Tstamp.c`, using the same
  integer widths as the C code (`int64_t beats`, `int32_t rem`). Lean's `Int64`
  and `Int32` wrap on overflow, while signed overflow is undefined in C, so the
  correctness theorems carry explicit no-overflow preconditions.

  Each operation is proved to agree with the mathematical model in
  `Kunquat.Tstamp`, and is exported to C with scalar-only arguments so that no
  Lean objects cross the boundary.
-/

namespace Kunquat

structure Tstamp64 where
  beats : Int64
  rem   : Int32
  deriving DecidableEq

namespace Tstamp64

def BEAT32 : Int32 := 882161280

/-- The mathematical timestamp a machine timestamp denotes. -/
noncomputable def toModel (ts : Tstamp64) : Tstamp := ⟨ts.beats.toInt, ts.rem.toInt⟩

/-- `Tstamp_add`, in machine integers. -/
@[inline]
def add (ts1 ts2 : Tstamp64) : Tstamp64 :=
  let beats := ts1.beats + ts2.beats
  let rem   := ts1.rem + ts2.rem
  if rem ≥ BEAT32 then ⟨beats + 1, rem - BEAT32⟩
  else if rem < 0 then ⟨beats - 1, rem + BEAT32⟩
  else ⟨beats, rem⟩

/-- `Tstamp_sub`, in machine integers. -/
@[inline]
def sub (ts1 ts2 : Tstamp64) : Tstamp64 :=
  let beats := ts1.beats - ts2.beats
  let rem   := ts1.rem - ts2.rem
  if rem < 0 then ⟨beats - 1, rem + BEAT32⟩
  else if rem ≥ BEAT32 then ⟨beats + 1, rem - BEAT32⟩
  else ⟨beats, rem⟩

/-- `Tstamp_cmp`, in machine integers. -/
@[inline]
def cmp (ts1 ts2 : Tstamp64) : Int32 :=
  if ts1.beats < ts2.beats then -1
  else if ts1.beats > ts2.beats then 1
  else if ts1.rem < ts2.rem then -1
  else if ts1.rem > ts2.rem then 1
  else 0

/-! ## Machine arithmetic is exact when it doesn't overflow -/

private theorem i64_add {x y : Int64} (h1 : -2^63 ≤ x.toInt + y.toInt)
    (h2 : x.toInt + y.toInt < 2^63) : (x + y).toInt = x.toInt + y.toInt := by
  rw [Int64.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem i64_sub {x y : Int64} (h1 : -2^63 ≤ x.toInt - y.toInt)
    (h2 : x.toInt - y.toInt < 2^63) : (x - y).toInt = x.toInt - y.toInt := by
  rw [Int64.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem i32_add {x y : Int32} (h1 : -2^31 ≤ x.toInt + y.toInt)
    (h2 : x.toInt + y.toInt < 2^31) : (x + y).toInt = x.toInt + y.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem i32_sub {x y : Int32} (h1 : -2^31 ≤ x.toInt - y.toInt)
    (h2 : x.toInt - y.toInt < 2^31) : (x - y).toInt = x.toInt - y.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem beat32_toInt : BEAT32.toInt = 882161280 := by decide
private theorem one64_toInt : (1 : Int64).toInt = 1 := by decide
private theorem zero32_toInt : (0 : Int32).toInt = 0 := by decide

/-- The no-overflow condition for `Tstamp_add`: the beat sum, with room for a
    carry, fits in `int64_t`. -/
def AddInRange (a b : Tstamp64) : Prop :=
  -2^63 < a.beats.toInt + b.beats.toInt ∧ a.beats.toInt + b.beats.toInt < 2^63 - 1

/-- The no-overflow condition for `Tstamp_sub`: the beat difference, with room
    for a borrow, fits in `int64_t`. -/
def SubInRange (a b : Tstamp64) : Prop :=
  -2^63 < a.beats.toInt - b.beats.toInt ∧ a.beats.toInt - b.beats.toInt < 2^63 - 1

/-! ## Agreement with the model -/

theorem add_correct {a b : Tstamp64} (ha : a.toModel.Valid) (hb : b.toModel.Valid)
    (hr : AddInRange a b) : (add a b).toModel = Tstamp.add a.toModel b.toModel := by
  simp only [toModel, Tstamp.Valid, BEAT, AddInRange] at *
  have hrem := i32_add (x := a.rem) (y := b.rem) (by omega) (by omega)
  have hbeats := i64_add (x := a.beats) (y := b.beats) (by omega) (by omega)
  simp only [add, Tstamp.add, BEAT]
  by_cases h1 : a.rem.toInt + b.rem.toInt ≥ 882161280
  · have c : a.rem + b.rem ≥ BEAT32 := by
      rw [ge_iff_le, Int32.le_iff_toInt_le, hrem, beat32_toInt]; omega
    have e1 : (a.beats + b.beats + 1).toInt = a.beats.toInt + b.beats.toInt + 1 := by
      rw [i64_add (by rw [hbeats, one64_toInt]; omega) (by rw [hbeats, one64_toInt]; omega),
        hbeats, one64_toInt]
    have e2 : (a.rem + b.rem - BEAT32).toInt = a.rem.toInt + b.rem.toInt - 882161280 := by
      rw [i32_sub (by rw [hrem, beat32_toInt]; omega) (by rw [hrem, beat32_toInt]; omega),
        hrem, beat32_toInt]
    simp only [c, h1, ite_true, e1, e2]
  · have c : ¬ (a.rem + b.rem ≥ BEAT32) := by
      rw [ge_iff_le, Int32.le_iff_toInt_le, hrem, beat32_toInt]; omega
    have c2 : ¬ (a.rem + b.rem < 0) := by
      rw [Int32.lt_iff_toInt_lt, hrem, zero32_toInt]; omega
    have h2 : ¬ (a.rem.toInt + b.rem.toInt < 0) := by omega
    simp only [c, c2, h1, h2, ite_false, hbeats, hrem]

theorem sub_correct {a b : Tstamp64} (ha : a.toModel.Valid) (hb : b.toModel.Valid)
    (hr : SubInRange a b) : (sub a b).toModel = Tstamp.sub a.toModel b.toModel := by
  simp only [toModel, Tstamp.Valid, BEAT, SubInRange] at *
  have hrem := i32_sub (x := a.rem) (y := b.rem) (by omega) (by omega)
  have hbeats := i64_sub (x := a.beats) (y := b.beats) (by omega) (by omega)
  simp only [sub, Tstamp.sub, BEAT]
  by_cases h1 : a.rem.toInt - b.rem.toInt < 0
  · have c : a.rem - b.rem < 0 := by
      rw [Int32.lt_iff_toInt_lt, hrem, zero32_toInt]; omega
    have e1 : (a.beats - b.beats - 1).toInt = a.beats.toInt - b.beats.toInt - 1 := by
      rw [i64_sub (by rw [hbeats, one64_toInt]; omega) (by rw [hbeats, one64_toInt]; omega),
        hbeats, one64_toInt]
    have e2 : (a.rem - b.rem + BEAT32).toInt = a.rem.toInt - b.rem.toInt + 882161280 := by
      rw [i32_add (by rw [hrem, beat32_toInt]; omega) (by rw [hrem, beat32_toInt]; omega),
        hrem, beat32_toInt]
    simp only [c, h1, ite_true, e1, e2]
  · have c : ¬ (a.rem - b.rem < 0) := by
      rw [Int32.lt_iff_toInt_lt, hrem, zero32_toInt]; omega
    have c2 : ¬ (a.rem - b.rem ≥ BEAT32) := by
      rw [ge_iff_le, Int32.le_iff_toInt_le, hrem, beat32_toInt]; omega
    have h2 : ¬ (a.rem.toInt - b.rem.toInt ≥ 882161280) := by omega
    simp only [c, c2, h1, h2, ite_false, hbeats, hrem]

/-- `cmp` needs no preconditions: comparisons cannot overflow. -/
theorem cmp_correct (a b : Tstamp64) :
    (cmp a b).toInt = Tstamp.cmp a.toModel b.toModel := by
  simp only [cmp, Tstamp.cmp, toModel, gt_iff_lt]
  simp only [Int64.lt_iff_toInt_lt, Int32.lt_iff_toInt_lt]
  repeat' split
  all_goals first | decide | omega

/-- The results are valid again, so operations can be chained. -/
theorem add_valid {a b : Tstamp64} (ha : a.toModel.Valid) (hb : b.toModel.Valid)
    (hr : AddInRange a b) : (add a b).toModel.Valid := by
  rw [add_correct ha hb hr]; exact Tstamp.add_valid ha hb

theorem sub_valid {a b : Tstamp64} (ha : a.toModel.Valid) (hb : b.toModel.Valid)
    (hr : SubInRange a b) : (sub a b).toModel.Valid := by
  rw [sub_correct ha hb hr]; exact Tstamp.sub_valid ha hb

/-! ## C interface

  Scalar arguments and results only: `Int64` and `Int32` are passed to and from
  C unboxed (as `uint64_t` and `uint32_t`), so there is no reference counting
  at the boundary. All functions are total on every input C can pass; the
  theorems above say when the results are meaningful.
-/

@[export kqt_lean_tstamp_add_beats]
def addBeats (b1 : Int64) (r1 : Int32) (b2 : Int64) (r2 : Int32) : Int64 :=
  (add ⟨b1, r1⟩ ⟨b2, r2⟩).beats

@[export kqt_lean_tstamp_add_rem]
def addRem (b1 : Int64) (r1 : Int32) (b2 : Int64) (r2 : Int32) : Int32 :=
  (add ⟨b1, r1⟩ ⟨b2, r2⟩).rem

@[export kqt_lean_tstamp_sub_beats]
def subBeats (b1 : Int64) (r1 : Int32) (b2 : Int64) (r2 : Int32) : Int64 :=
  (sub ⟨b1, r1⟩ ⟨b2, r2⟩).beats

@[export kqt_lean_tstamp_sub_rem]
def subRem (b1 : Int64) (r1 : Int32) (b2 : Int64) (r2 : Int32) : Int32 :=
  (sub ⟨b1, r1⟩ ⟨b2, r2⟩).rem

@[export kqt_lean_tstamp_cmp]
def cmpExport (b1 : Int64) (r1 : Int32) (b2 : Int64) (r2 : Int32) : Int32 :=
  cmp ⟨b1, r1⟩ ⟨b2, r2⟩

end Tstamp64
end Kunquat
