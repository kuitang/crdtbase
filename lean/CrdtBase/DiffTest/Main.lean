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
  let cmd : LwwMergeCmd ← fromJson? json
  if cmd.type != "lww_merge" then
    throw s!"unsupported command: {cmd.type}"
  let a ← toLww cmd.a
  let b ← toLww cmd.b
  if Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .eq && a.val != b.val then
    throw "conflicting LWW event identity: same (hlc, site) with different payloads"
  let result := LwwRegister.merge a b
  let out : LwwMergeResult := { result := fromLww result }
  pure ((toJson out).compress)

def emitLine (line : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr line
  stdout.putStr "\n"
  stdout.flush

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    pure ()
  else
    let trimmed := line.trimAscii
    if trimmed.isEmpty then
      loop stdin
    else
      match handleLine trimmed.copy with
      | Except.ok out => emitLine out
      | Except.error err =>
          emitLine <| (Json.mkObj [("error", toJson err)]).compress
      loop stdin

def main : IO Unit := do
  let stdin ← IO.getStdin
  loop stdin
