/-
  A sequencer for a subset of Kunquat, written to produce the same event
  stream as the C player (`Player_process_cgiters` in
  `src/lib/player/Player_seq.c`), so that the two can be compared.

  ## Subset

  * An order list of pattern instances, each a different pattern (instance 0).
  * Patterns with several columns. Rows are on quarter-beat boundaries and are
    counted in quarter beats.
  * Triggers: `n+` (note on, passed through), `m.t` (tempo), `m.jc`, `m.jp`,
    `m.jr` and `mj` (jumps).
  * Audio rate 4800 and tempos that divide 72000, so that every row starts on
    a whole frame: a quarter beat is `72000 / tempo` frames.

  ## Order of processing

  Playback visits *rows*: the times at which any column of the current
  pattern instance has triggers. Within a row, channels are processed in
  order, and within a channel its triggers in order. Each processed trigger
  is reported, with the frame at which it happens. Time advances only between
  rows; a jump takes no time and restarts processing at the first channel of
  the target row.

  Jump contexts are kept per trigger slot (pattern, row, channel, index), as
  in `Kunquat/Jump.lean`: a trigger slot with a context is skipped, not
  reported, and either jumps or removes its exhausted context.
-/

namespace Kunquat.Seq

/-- Quarter-beat units per beat, and the Tstamp remainder of a quarter beat. -/
def QUARTER_REM : Nat := 882161280 / 4

inductive Event where
  | noteOn (pitch : Int)
  | tempo (bpm : Nat)
  | jumpCounter (n : Nat)
  /-- Target pattern; instance 0. -/
  | jumpPattern (pat : Nat)
  /-- Target row in quarter beats. -/
  | jumpRow (row : Nat)
  | jump
  deriving Repr, BEq

structure Trigger where
  col : Nat
  /-- Row in quarter beats. -/
  row : Nat
  ev  : Event
  deriving Repr

structure Pattern where
  /-- Length in quarter beats. -/
  len  : Nat
  /-- In the order they appear within each column. -/
  trigs : List Trigger
  deriving Repr

structure Module where
  patterns : Array Pattern
  /-- Pattern numbers in playback order. -/
  order : List Nat
  deriving Repr

/-- A trigger slot that may hold a jump context. -/
structure Slot where
  pat : Nat
  row : Nat
  col : Nat
  idx : Nat
  deriving BEq, Repr

structure JumpCtx where
  slot   : Slot
  count  : Nat
  tpat   : Nat
  trow   : Nat
  deriving Repr

structure State where
  /-- Index into the order list. -/
  oi      : Nat
  row     : Nat
  frame   : Nat
  tempo   : Nat
  counter : Nat
  /-- `none` until `m.jp` is set: jump within the current pattern instance. -/
  tpat    : Option Nat
  trow    : Nat
  ctxs    : List JumpCtx
  deriving Repr

/-- A reported event: frame, channel, event. -/
abbrev Report := Nat × Nat × Event

def State.init : State := ⟨0, 0, 0, 120, 0, none, 0, []⟩

def quarterFrames (tempo : Nat) : Nat := 72000 / tempo

def Module.pattern (m : Module) (p : Nat) : Pattern :=
  m.patterns.getD p ⟨0, []⟩

def Module.patAt (m : Module) (oi : Nat) : Option Nat := m.order[oi]?

/-- The trigger slots of a row, in processing order: by column, then in order
    within the column. -/
def rowSlots (p : Pattern) (pat row : Nat) : List (Slot × Event) :=
  let here := p.trigs.filter (·.row == row)
  let cols := (here.map (·.col)).eraseDups.mergeSort (· ≤ ·)
  cols.flatMap fun c =>
    ((here.filter (·.col == c)).zipIdx).map fun (t, i) => (⟨pat, row, c, i⟩, t.ev)

/-- The next row with triggers after `row`, or the pattern end. -/
def nextRow (p : Pattern) (row : Nat) : Nat :=
  (p.trigs.map (·.row)).foldl (fun acc r => if r > row && r < acc then r else acc) p.len

/-- What processing the triggers of the current row leads to. -/
inductive RowEnd where
  /-- All triggers processed: move on to the next row. -/
  | done
  /-- Jump to a row of a pattern. -/
  | jumpTo (pat row : Nat)

/-- Process the given slots of the current row. -/
def processSlots (pat : Nat) :
    List (Slot × Event) → State → List Report → State × List Report × RowEnd
  | [], s, out => (s, out, .done)
  | (slot, ev) :: rest, s, out =>
    match s.ctxs.find? (·.slot == slot) with
    | some j =>
      if j.count > 0 then
        let ctxs := s.ctxs.map fun k => if k.slot == slot then { k with count := k.count - 1 } else k
        ({ s with ctxs }, out, .jumpTo j.tpat j.trow)
      else
        processSlots pat rest { s with ctxs := s.ctxs.filter (·.slot != slot) } out
    | none =>
      let out := (s.frame, slot.col, ev) :: out
      match ev with
      | .noteOn _ => processSlots pat rest s out
      | .tempo t => processSlots pat rest { s with tempo := t } out
      | .jumpCounter n => processSlots pat rest { s with counter := n } out
      | .jumpPattern p => processSlots pat rest { s with tpat := some p } out
      | .jumpRow r => processSlots pat rest { s with trow := r } out
      | .jump =>
        if s.counter > 0 then
          let tp := s.tpat.getD pat
          let j : JumpCtx := ⟨slot, s.counter - 1, tp, s.trow⟩
          ({ s with ctxs := j :: s.ctxs }, out, .jumpTo tp s.trow)
        else
          processSlots pat rest s out

/-- Play the module. Returns the reported events in order and the total
    length in frames, or `none` if playback takes more than `fuel` rows. -/
def play (m : Module) : (fuel : Nat) → State → List Report → Option (List Report × Nat)
  | 0, _, _ => none
  | fuel + 1, s, out =>
    match m.patAt s.oi with
    | none => some (out.reverse, s.frame)
    | some pat =>
      let p := m.pattern pat
      let (s, out, e) := processSlots pat (rowSlots p pat s.row) s out
      match e with
      | .jumpTo tp tr =>
        match m.order.idxOf? tp with
        | some oi => play m fuel { s with oi, row := tr } out
        -- The C player stops if the jump target is not in the order list.
        | none => some (out.reverse, s.frame)
      | .done =>
        let next := nextRow p s.row
        let s := { s with frame := s.frame + (next - s.row) * quarterFrames s.tempo }
        if next ≥ p.len then
          play m fuel { s with oi := s.oi + 1, row := 0 } out
        else
          play m fuel { s with row := next } out

/-! ## Output in the C player's JSON format -/

def Event.toJson : Event → String
  | .noteOn x => s!"[\"n+\", {x}]"
  | .tempo t => s!"[\"m.t\", {t}]"
  | .jumpCounter n => s!"[\"m.jc\", {n}]"
  | .jumpPattern p => s!"[\"m.jp\", [{p}, 0]]"
  | .jumpRow r => s!"[\"m.jr\", [{r / 4}, {(r % 4) * QUARTER_REM}]]"
  | .jump => "[\"mj\", null]"

end Kunquat.Seq
