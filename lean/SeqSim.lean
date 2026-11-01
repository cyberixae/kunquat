/-
  Reads a module description from standard input, plays it with the Lean
  sequencer (`Kunquat/Seq.lean`) and prints the reported events, one per line
  as `<frame> <channel> <event JSON>`, followed by `end <total frames>`.
  Used by `test/seq_diff.py` to compare with the C player.

  Input lines:

  * `order <pattern> ...`: the order list
  * `pattern <pattern> <length in quarter beats>`
  * `trig <pattern> <column> <row in quarter beats> <event> [<argument>]`,
    where the event is `n+`, `m.t`, `m.jc`, `m.jp` (pattern number), `m.jr`
    (row in quarter beats) or `mj`. Triggers of a column must be listed in
    order.

  Usage: seqsim [max rows]. Exits with status 3 if playback visits more rows
  (default 100000).
-/
import Kunquat.Seq

open Kunquat.Seq

def words (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

def parseEvent : List String → Option Event
  | ["n+", x] => x.toInt?.map .noteOn
  | ["m.t", x] => x.toNat?.map .tempo
  | ["m.jc", x] => x.toNat?.map .jumpCounter
  | ["m.jp", x] => x.toNat?.map .jumpPattern
  | ["m.jr", x] => x.toNat?.map .jumpRow
  | ["mj"] => some .jump
  | _ => none

def parse (lines : List String) : Option Module := do
  let mut pats : Array Pattern := #[]
  let mut order : List Nat := []
  for line in lines do
    match words line with
    | [] => pure ()
    | "order" :: ps => order ← ps.mapM (·.toNat?)
    | ["pattern", p, len] =>
      let p ← p.toNat?
      let len ← len.toNat?
      while pats.size ≤ p do pats := pats.push ⟨0, []⟩
      pats := pats.modify p fun pt => { pt with len }
    | "trig" :: p :: col :: row :: ev =>
      let p ← p.toNat?
      let t : Trigger := ⟨← col.toNat?, ← row.toNat?, ← parseEvent ev⟩
      while pats.size ≤ p do pats := pats.push ⟨0, []⟩
      pats := pats.modify p fun pt => { pt with trigs := pt.trigs ++ [t] }
    | _ => none
  pure ⟨pats, order⟩

def main (args : List String) : IO UInt32 := do
  let fuel := (args.head?.bind (·.toNat?)).getD 100000
  let input ← (← IO.getStdin).readToEnd
  let some m := parse (input.splitOn "\n")
    | IO.eprintln "bad module description"; return 2
  match play m fuel State.init [] with
  | some (reports, frames) =>
    for (frame, ch, ev) in reports do
      IO.println s!"{frame} {ch} {ev.toJson}"
    IO.println s!"end {frames}"
    return 0
  | none => IO.eprintln "too long"; return 3
