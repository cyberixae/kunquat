/-
  Reads a song from standard input and prints the playback time the jump model
  predicts, in beats. Used by `test/jump_diff.py` to compare the model with the
  C player.

  Input: the song length in beats on the first line, then one trigger slot per
  line in playback order: `<row> jc <count>`, `<row> jr <row>` or `<row> mj`.
-/
import Kunquat.Jump

open Kunquat.Jump

def trim (s : String) : String := s.trimAscii.toString

def parseSlot (line : String) : Option (Nat × String × Nat) :=
  match (line.splitOn " ").filter (· ≠ "") with
  | [r, "mj"] => r.toNat?.map (·, "mj", 0)
  | [r, k, a] => do pure (← r.toNat?, k, ← a.toNat?)
  | _ => none

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  let lines := (input.splitOn "\n").filter (trim · ≠ "")
  let some len := lines.head?.bind (trim · |>.toNat?)
    | IO.eprintln "bad length"; return 2
  let slots := (lines.drop 1).filterMap (parseSlot <| trim ·)
  if slots.length != lines.length - 1 then
    IO.eprintln "bad slot line"; return 2
  let arr := slots.toArray
  let rowOf (p : Nat) : Nat := if h : p < arr.size then arr[p].1 else len
  -- A jump to row r lands on the first slot at or after r.
  let slotOf (r : Nat) : Nat := (arr.findIdx? (·.1 ≥ r)).getD arr.size
  let song : Song := {
    size := arr.size
    trigger := fun p =>
      if h : p < arr.size then
        match arr[p].2 with
        | ("jc", c) => .setCounter (fun _ => c)
        | ("jr", r) => .setTarget (slotOf r)
        | ("mj", _) => .jump
        | _ => .other
      else .other }
  match elapsed song rowOf len 10000000 (State.init (slotOf 0)) 0 with
  | some t => IO.println t; return 0
  | none => IO.eprintln "out of fuel"; return 1
