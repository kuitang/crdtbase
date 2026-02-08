import Lean
import CrdtBase.Hlc.Defs
import CrdtBase.Crdt.Lww.Defs

set_option autoImplicit false

open Lean
open CrdtBase

structure HlcJson where
  wallMs : Nat
  counter : Nat
  deriving FromJson, ToJson

structure LwwJson where
  val : Json
  hlc : HlcJson
  site : String
  deriving FromJson, ToJson

structure LwwMergeCmd where
  type : String
  a : LwwJson
  b : LwwJson
  deriving FromJson

structure LwwMergeResult where
  result : LwwJson
  deriving ToJson

def toHlc (h : HlcJson) : Except String Hlc := do
  match Hlc.mk? h.wallMs h.counter with
  | some hlc => pure hlc
  | none => throw s!"invalid HLC bounds: {h.wallMs} {h.counter}"

def toLww (l : LwwJson) : Except String (LwwRegister Json) := do
  let hlc ← toHlc l.hlc
  pure { val := l.val, hlc := hlc, site := l.site }

def fromLww (l : LwwRegister Json) : LwwJson :=
  { val := l.val
    hlc := { wallMs := l.hlc.wallMs, counter := l.hlc.counter }
    site := l.site }

def handleLine (line : String) : Except String String := do
  let json ← Json.parse line
  let cmd ← fromJson? LwwMergeCmd json
  if cmd.type != "lww_merge" then
    throw s!"unsupported command: {cmd.type}"
  let a ← toLww cmd.a
  let b ← toLww cmd.b
  let result := LwwRegister.merge a b
  let out : LwwMergeResult := { result := fromLww result }
  pure (Json.toString (toJson out))

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  if (← stdin.isEof) then
    pure ()
  else
    let line ← stdin.getLine
    let trimmed := line.trim
    if trimmed.isEmpty then
      loop stdin
    else
      match handleLine trimmed with
      | Except.ok out => IO.println out
      | Except.error err => throw <| IO.userError err
      loop stdin

def main : IO Unit := do
  let stdin ← IO.getStdin
  loop stdin
