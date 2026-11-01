/-
  A model of the jump state machine in `src/lib/player/Player_seq.c`
  (`Player_process_cgiters`) and `src/lib/player/events/Event_master_jump.c`.

  ## What is modelled

  Playback visits trigger slots in order. A *position* is the index of one
  trigger slot in playback order: pattern instance, then row, then channel,
  then trigger index within the row. Jump targets are positions too (the first
  trigger slot at or after the target row).

  Only the triggers that affect jumping are distinguished:

  * `m.jc` sets the master jump counter,
  * `m.jp` / `m.jr` set the master jump target,
  * `mj` jumps,
  * everything else just moves playback on.

  Control events (`cg`, `cpattern`, ...) are ignored in triggers unless
  infinite mode is enabled (see the specification), so they are not modelled.
  This is the finite playback mode; infinite mode does not terminate by design.

  A jump context records, for one position, how many jumps are left and where
  to jump. When playback reaches a position:

  * If there is a context there, the trigger itself is skipped. If the context
    has jumps left, one is used and playback moves to its target; otherwise
    the context is removed and playback continues.
  * Otherwise the trigger is processed. `mj` with a positive jump counter `n`
    creates a context with `n - 1` jumps left and jumps immediately.

  So `[m.jc n] ... [mj]` jumps back `n` times, as the specification describes.

  ## Difference from the C code

  The C code looks up the next jump context once per render slice, within the
  current pattern instance. If a slice starts at the end of one pattern
  instance and continues into the next, an existing context there is missed
  and `mj` tries to create a second context at the same position, which fails
  an assertion in `AAtree_attach` (see `test/jump_context_crash.c`). The model
  always reads the current state, so it describes the intended behaviour.
-/

namespace Kunquat.Jump

/-- A jump context (`Jump_context` in the C code). -/
structure Ctx where
  count  : Nat
  target : Nat

structure State where
  pos     : Nat
  /-- `Master_params.jump_counter` -/
  counter : Nat
  /-- `Master_params.jump_target_piref` and `jump_target_row` -/
  target  : Nat
  /-- `Master_params.active_jumps`: at most one context per position. -/
  ctx     : Nat → Option Ctx

inductive Trigger where
  /-- `m.jc`: set the jump counter. The argument is an expression in Kunquat,
      so the value may depend on the playback state; the C validator limits
      it to `[0, 32767]`. -/
  | setCounter (value : State → Nat)
  /-- `m.jp` / `m.jr`: set the jump target. -/
  | setTarget (target : Nat)
  /-- `mj`: jump. -/
  | jump
  /-- Any other trigger. -/
  | other

structure Song where
  /-- Number of trigger slots. Playback ends when the position reaches it. -/
  size    : Nat
  trigger : Nat → Trigger

/-- Every `m.jc` value is at most `C`. For Kunquat, `C = 32767`. -/
def Song.Bounded (song : Song) (C : Nat) : Prop :=
  ∀ p f s, song.trigger p = .setCounter f → f s ≤ C

/-- Playback from the start of the song: no jump contexts, and the jump
    counter and target at their defaults. -/
def State.init (target : Nat := 0) : State :=
  ⟨0, 0, target, fun _ => none⟩

def State.setCtx (s : State) (p : Nat) (c : Option Ctx) : Nat → Option Ctx :=
  fun q => if q = p then c else s.ctx q

/-- One step of playback: process the trigger slot at the current position. -/
def step (song : Song) (s : State) : State :=
  match s.ctx s.pos with
  | some j =>
    -- At an active jump: the trigger is skipped.
    if j.count > 0 then
      { s with ctx := s.setCtx s.pos (some { j with count := j.count - 1 }),
               pos := j.target }
    else
      { s with ctx := s.setCtx s.pos none, pos := s.pos + 1 }
  | none =>
    match song.trigger s.pos with
    | .setCounter f => { s with counter := f s, pos := s.pos + 1 }
    | .setTarget t  => { s with target := t, pos := s.pos + 1 }
    | .jump =>
      if s.counter > 0 then
        -- `Event_master_jump_process` creates the context with the current
        -- counter, then the sequencer decrements it and jumps.
        { s with ctx := s.setCtx s.pos (some ⟨s.counter - 1, s.target⟩),
                 pos := s.target }
      else
        { s with pos := s.pos + 1 }
    | .other => { s with pos := s.pos + 1 }

/-- Run for at most `n` steps, stopping at the end of the song. -/
def stepN (song : Song) : Nat → State → State
  | 0, s => s
  | n + 1, s => if s.pos < song.size then stepN song n (step song s) else s

/-- The positions visited in at most `n` steps. For examples and testing. -/
def trace (song : Song) : Nat → State → List Nat
  | 0, _ => []
  | n + 1, s => if s.pos < song.size then s.pos :: trace song n (step song s) else []

/-! ## Invariant: counters stay bounded -/

def Inv (C : Nat) (s : State) : Prop :=
  s.counter ≤ C ∧ ∀ p j, s.ctx p = some j → j.count ≤ C

theorem Inv.init (C t : Nat) : Inv C (State.init t) :=
  ⟨Nat.zero_le _, fun _ _ h => by simp [State.init] at h⟩

theorem step_inv {song : Song} {C : Nat} (hsong : song.Bounded C) {s : State}
    (hs : Inv C s) : Inv C (step song s) := by
  obtain ⟨hc, hctx⟩ := hs
  unfold step
  split
  · next j hj =>
    have := hctx _ _ hj
    split
    · refine ⟨hc, fun p j' h => ?_⟩
      simp only [State.setCtx] at h
      split at h
      · cases h; simp only; omega
      · exact hctx _ _ h
    · refine ⟨hc, fun p j' h => ?_⟩
      simp only [State.setCtx] at h
      split at h
      · cases h
      · exact hctx _ _ h
  · split
    · next f hf => exact ⟨hsong _ f s hf, hctx⟩
    · exact ⟨hc, hctx⟩
    · split
      · refine ⟨hc, fun p j' h => ?_⟩
        simp only [State.setCtx] at h
        split at h
        · cases h; simp only; omega
        · exact hctx _ _ h
      · exact ⟨hc, hctx⟩
    · exact ⟨hc, hctx⟩

/-! ## A step only changes the context at the current position -/

theorem step_ctx_other (song : Song) (s : State) (q : Nat) (hq : q ≠ s.pos) :
    (step song s).ctx q = s.ctx q := by
  unfold step
  split
  · split <;> simp [State.setCtx, hq]
  · split
    · rfl
    · rfl
    · split
      · simp [State.setCtx, hq]
      · rfl
    · rfl

/-! ## The termination measure

  For each position `p`, a digit `phi s p`:

  * `0` if playback is already past `p`: then `p` cannot act again unless a
    jump from a later position brings playback back;
  * `count + 1` if `p` has a jump context with `count` jumps left;
  * `C + 2` if `p` has no context: reaching it may create one.

  Every step lowers the digit at the current position and does not raise the
  digit of any later position. Reading the digits as a number in base `C + 3`
  with later positions more significant, every step lowers the number.
-/

def phi (C : Nat) (s : State) (p : Nat) : Nat :=
  if s.pos > p then 0
  else match s.ctx p with
    | some j => j.count + 1
    | none => C + 2

theorem phi_lt {C : Nat} {s : State} (hs : Inv C s) (p : Nat) : phi C s p < C + 3 := by
  unfold phi
  split
  · omega
  · split
    · next j hj => have := hs.2 _ _ hj; omega
    · omega

/-- Later positions: their digit can only go down. -/
theorem phi_step_later (song : Song) (C : Nat) (s : State) (q : Nat) (hq : s.pos < q) :
    phi C (step song s) q ≤ phi C s q := by
  have hctx := step_ctx_other song s q (by omega)
  unfold phi
  have : ¬ (s.pos > q) := by omega
  simp only [this, ite_false, hctx]
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- The current position: its digit goes down. -/
theorem phi_step_here {song : Song} {C : Nat} {s : State} (hs : Inv C s) :
    phi C (step song s) s.pos < phi C s s.pos := by
  have hnot : ¬ (s.pos > s.pos) := Nat.lt_irrefl _
  unfold step
  split
  · next j hj =>
    split
    · -- jump using the context
      simp only [phi, hnot, ite_false, hj, State.setCtx, ite_true]
      split <;> omega
    · -- exhausted context removed, playback moves on
      simp only [phi, hnot, ite_false, hj]
      have : s.pos + 1 > s.pos := Nat.lt_succ_self _
      simp only [this, ite_true]; omega
  · next hj =>
    have hfwd : ∀ x : Nat, (if s.pos + 1 > s.pos then 0 else x) < C + 2 := by
      intro x; simp
    split
    · simp only [phi, hnot, ite_false, hj]; exact hfwd _
    · simp only [phi, hnot, ite_false, hj]; exact hfwd _
    · split
      · -- jump creates a context
        simp only [phi, hnot, ite_false, hj, State.setCtx, ite_true]
        have := hs.1
        split <;> omega
      · simp only [phi, hnot, ite_false, hj]; exact hfwd _
    · simp only [phi, hnot, ite_false, hj]; exact hfwd _

/-! ## Digits in base `B` -/

/-- `enc f B n = f 0 * B^0 + f 1 * B^1 + ... + f (n-1) * B^(n-1)` -/
def enc (f : Nat → Nat) (B : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => enc f B n + f n * B ^ n

theorem enc_lt_pow {f : Nat → Nat} {B : Nat} (hf : ∀ q, f q < B) :
    ∀ n, enc f B n < B ^ n
  | 0 => by simp [enc]
  | n + 1 => by
    have ih := enc_lt_pow hf n
    have h1 : f n * B ^ n ≤ (B - 1) * B ^ n :=
      Nat.mul_le_mul_right _ (by have := hf n; omega)
    have h2 : (B - 1) * B ^ n + B ^ n = B ^ (n + 1) := by
      have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hf 0)
      rw [Nat.pow_succ, ← Nat.succ_mul, Nat.mul_comm]
      congr 1; omega
    simp only [enc]; omega

/-- If the highest digit that changes goes down, the number goes down. -/
theorem enc_lt_of_digit {f g : Nat → Nat} {B : Nat} (hg : ∀ q, g q < B) {p : Nat}
    (hlt : g p < f p) (hle : ∀ q, p < q → g q ≤ f q) :
    ∀ n, p < n → enc g B n < enc f B n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [enc]
    by_cases hpn : p = n
    · subst hpn
      have h1 := enc_lt_pow hg p
      have h2 : (g p + 1) * B ^ p ≤ f p * B ^ p := Nat.mul_le_mul_right _ hlt
      rw [Nat.succ_mul] at h2
      omega
    · have ih := enc_lt_of_digit hg hlt hle n (by omega)
      have h2 : g n * B ^ n ≤ f n * B ^ n := Nat.mul_le_mul_right _ (hle n (by omega))
      omega

/-- The termination measure. -/
def measure (C : Nat) (song : Song) (s : State) : Nat :=
  enc (phi C s) (C + 3) song.size

/-- Every step before the end of the song lowers the measure. -/
theorem measure_step {song : Song} {C : Nat} {s : State} (hs : Inv C s)
    (hpos : s.pos < song.size) :
    measure C song (step song s) < measure C song s :=
  enc_lt_of_digit (phi_lt (step_inv_any hs)) (phi_step_here hs)
    (fun q hq => phi_step_later song C s q hq) song.size hpos
where
  /-- `phi_lt` for the next state needs only the bound on context counts,
      which a step preserves whatever the song. -/
  step_inv_any {s : State} (hs : Inv C s) : Inv C ⟨(step song s).pos, 0,
      (step song s).target, (step song s).ctx⟩ := by
    refine ⟨Nat.zero_le _, fun p j h => ?_⟩
    simp only at h
    unfold step at h
    split at h
    · next j0 hj0 =>
      have := hs.2 _ _ hj0
      split at h <;> simp only [State.setCtx] at h <;> split at h
      · cases h; simp only; omega
      · exact hs.2 _ _ h
      · cases h
      · exact hs.2 _ _ h
    · split at h
      · exact hs.2 _ _ h
      · exact hs.2 _ _ h
      · split at h
        · simp only [State.setCtx] at h
          split at h
          · cases h; simp only; have := hs.1; omega
          · exact hs.2 _ _ h
        · exact hs.2 _ _ h
      · exact hs.2 _ _ h

/-! ## Termination -/

/-- Playback, as a total function. Lean accepts the recursion only because
    `measure_step` shows that every step lowers the measure. -/
def play (C : Nat) (song : Song) (hsong : song.Bounded C) (s : State) (hs : Inv C s) :
    State :=
  if _h : s.pos < song.size then
    play C song hsong (step song s) (step_inv hsong hs)
  else
    s
termination_by measure C song s
decreasing_by exact measure_step hs (by assumption)

/-- Playback always reaches the end of the song: no combination of jumps,
    nested or crossing, with any `m.jc` values, can loop forever. -/
theorem play_ends (C : Nat) (song : Song) (hsong : song.Bounded C) (s : State)
    (hs : Inv C s) : ¬ (play C song hsong s hs).pos < song.size := by
  rw [play]
  split
  · exact play_ends C song hsong (step song s) (step_inv hsong hs)
  · next h => exact h
termination_by measure C song s
decreasing_by exact measure_step hs (by assumption)

/-- An explicit bound: playback ends within `measure` steps, and the measure
    is less than `(C + 3) ^ size`. -/
theorem ends_within {song : Song} {C : Nat} (hsong : song.Bounded C) :
    ∀ (n : Nat) (s : State), Inv C s → measure C song s ≤ n →
      ¬ (stepN song n s).pos < song.size
  | 0, s, hs, hm => by
    simp only [stepN]
    intro hpos
    have := measure_step hs hpos
    omega
  | n + 1, s, hs, hm => by
    simp only [stepN]
    split
    · next hpos =>
      exact ends_within hsong n _ (step_inv hsong hs)
        (by have := measure_step hs hpos; omega)
    · next hpos => exact hpos

theorem measure_lt {song : Song} {C : Nat} {s : State} (hs : Inv C s) :
    measure C song s < (C + 3) ^ song.size :=
  enc_lt_pow (phi_lt hs) song.size

/-! ## Examples

  Each slot of a song below is one trigger, in playback order.
-/

/-- The song from `test/jump_context_crash.c`: an empty pattern instance P0,
    then P1 with `[m.jc 1] [m.jp P0] [mj]` on row 0. The jump target is
    position 0 (P0 has no triggers, so its first slot is P1's first). -/
def crashSong : Song where
  size := 3
  trigger
    | 0 => .setCounter (fun _ => 1)
    | 1 => .setTarget 0
    | 2 => .jump
    | _ => .other

/-- P1 row 0 plays twice: once before the jump, once after it. -/
example : trace crashSong 100 State.init = [0, 1, 2, 0, 1, 2] := by decide

/-- Nested loops: an inner `mj` jumping back twice to slot 1, inside an outer
    `mj` jumping back once to slot 0. The inner context is removed when it is
    exhausted, so each outer pass arms it afresh. -/
def nestedSong : Song where
  size := 7
  trigger
    | 0 => .other            -- outer loop start
    | 1 => .setTarget 1      -- inner target: slot 1
    | 2 => .setCounter (fun _ => 2)
    | 3 => .jump             -- inner mj: 2 jumps back to slot 1
    | 4 => .setTarget 0      -- outer target: slot 0
    | 5 => .setCounter (fun _ => 1)
    | 6 => .jump             -- outer mj: 1 jump back to slot 0
    | _ => .other

/-- The inner loop runs 3 times per outer pass, and the outer loop twice. -/
example : trace nestedSong 100 State.init =
    [0, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4, 5, 6,
     0, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4, 5, 6] := by decide

end Kunquat.Jump

namespace Kunquat.Jump

/-! ## Playback time

  For comparing the model with the C player: each slot has a row time, and a
  jump takes no time. Playback time therefore advances only as the cursor
  moves forward between slots, and to the pattern end after the last slot.
-/

/-- Whether the step from `s` is a jump (as opposed to moving on). -/
def isJump (song : Song) (s : State) : Bool :=
  match s.ctx s.pos with
  | some j => j.count > 0
  | none =>
    match song.trigger s.pos with
    | .jump => s.counter > 0
    | _ => false

/-- Total playback time, given the row time of each slot and the song length,
    or `none` if `fuel` steps are not enough. `now` is the cursor's current
    time position. -/
def elapsed (song : Song) (row : Nat → Nat) (len : Nat) :
    (fuel : Nat) → (s : State) → (now : Nat) → Option Nat
  | 0, _, _ => none
  | fuel + 1, s, now =>
    if s.pos < song.size then
      let t := row s.pos
      let s' := step song s
      let now' := if isJump song s then row s'.pos else t
      (elapsed song row len fuel s' now').map ((t - now) + ·)
    else
      some (len - now)

end Kunquat.Jump
