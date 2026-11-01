/-
  Reads a song from standard input and prints the playback time the jump model
  predicts, in beats. Used by `test/jump_diff.py` to compare the model with the
  C player.

  Input: the lengths in beats of the song's pattern instances, in playback
  order, on the first line. Then one trigger line per line in playback order,
  each starting with its time in beats from the start of the song:

  * `<time> jc <count>`: `m.jc`
  * `<time> jr <row>`: `m.jr` in a one-pattern song
  * `<time> jt <time>`: `m.jp` followed by `m.jr`, setting the jump target to a
    time anywhere in the song (two trigger slots)
  * `<time> mj`: `mj`

  Usage: jumpsim [max steps]. Exits with status 3 if playback takes more steps
  (default 20000); nested jumps can make playback exponentially long.
-/
import Kunquat.Jump

open Kunquat.Jump

def trim (s : String) : String := s.trimAscii.toString

def words (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

def parseLine (line : String) : Option (List (Nat × String × Nat)) :=
  match words line with
  | [t, "mj"] => t.toNat?.map fun t => [(t, "mj", 0)]
  | [t, "jt", a] => do
    let t ← t.toNat?
    pure [(t, "jp", 0), (t, "jr", ← a.toNat?)]
  | [t, k, a] => do pure [(← t.toNat?, k, ← a.toNat?)]
  | _ => none

def main (args : List String) : IO UInt32 := do
  let fuel := (args.head?.bind (·.toNat?)).getD 20000
  let input ← (← IO.getStdin).readToEnd
  let lines := (input.splitOn "\n").filter (trim · ≠ "")
  let some lens := lines.head?.bind fun l => (words (trim l)).mapM (·.toNat?)
    | IO.eprintln "bad length line"; return 2
  let len := lens.foldl (· + ·) 0
  let some slots := ((lines.drop 1).mapM (parseLine <| trim ·)).map List.flatten
    | IO.eprintln "bad trigger line"; return 2
  -- Jumps land on a row, which may have no triggers. Add an empty slot at
  -- every jump target time without one, so that the target slot's time is
  -- the target time. Empty slots do not affect jumping.
  let targets := 0 :: slots.filterMap fun (_, k, a) => if k == "jr" then some a else none
  let missing := (targets.filter fun t => !slots.any (·.1 == t)).eraseDups
  let slots := missing.foldl (init := slots) fun acc t =>
    let (before, after) := acc.span (·.1 < t)
    before ++ (t, "nop", 0) :: after
  let arr := slots.toArray
  let timeOf (p : Nat) : Nat := if h : p < arr.size then arr[p].1 else len
  -- A jump to time t lands on the first slot at or after t.
  let slotOf (t : Nat) : Nat := (arr.findIdx? (·.1 ≥ t)).getD arr.size
  let song : Song := {
    size := arr.size
    trigger := fun p =>
      if h : p < arr.size then
        match arr[p].2 with
        | ("jc", c) => .setCounter (fun _ => c)
        | ("jr", t) => .setTarget (slotOf t)
        | ("mj", _) => .jump
        | _ => .other
      else .other }
  match elapsed song timeOf len fuel (State.init (slotOf 0)) 0 with
  | some t => IO.println t; return 0
  | none => IO.eprintln "too long"; return 3
