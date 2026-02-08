import Batteries

namespace CrdtBase

/-- Upper bound (exclusive) for the 48-bit wall clock millis. -/
def wallMsMax : Nat := 2 ^ 48

/-- Upper bound (exclusive) for the 16-bit logical counter. -/
def counterMax : Nat := 2 ^ 16

/-- Maximum clock drift (in milliseconds) accepted by recv. -/
def driftLimitMs : Nat := 60_000

/-- A bounded Hybrid Logical Clock timestamp. -/
structure Hlc where
  wallMs : Nat
  counter : Nat
  wallMs_lt : wallMs < wallMsMax
  counter_lt : counter < counterMax
  deriving Repr, DecidableEq

namespace Hlc

/-- Pack an HLC into a single natural number for comparison. -/
def pack (h : Hlc) : Nat :=
  h.wallMs * counterMax + h.counter

/-- Total order on HLCs: compare packed values. -/
instance : Ord Hlc where
  compare a b := compare a.pack b.pack

/-- Construct an HLC only if both fields are within bounds. -/
def mk? (wallMs counter : Nat) : Option Hlc :=
  if hWall : wallMs < wallMsMax then
    if hCounter : counter < counterMax then
      some ⟨wallMs, counter, hWall, hCounter⟩
    else
      none
  else
    none

/-- Helper: maximum of three natural numbers. -/
def max3 (a b c : Nat) : Nat :=
  max a (max b c)

/-- Compute the wall clock component for a recv. -/
def recvWall (local remote : Hlc) (now : Nat) : Nat :=
  max3 local.wallMs remote.wallMs now

/-- Compute the logical counter component for a recv. -/
def recvCounter (local remote : Hlc) (now : Nat) : Nat :=
  let wall := recvWall local remote now
  if hLocal : wall = local.wallMs then
    if hRemote : wall = remote.wallMs then
      max local.counter remote.counter + 1
    else
      local.counter + 1
  else if hRemote : wall = remote.wallMs then
    remote.counter + 1
  else
    0

/-- Advance the local HLC based on a local event. -/
def now (local : Hlc) (wall : Nat) : Option Hlc :=
  let wall' := max local.wallMs wall
  let counter :=
    if wall' = local.wallMs then
      local.counter + 1
    else
      0
  mk? wall' counter

/-- Receive a remote HLC, rejecting on excessive clock drift. -/
def recv (local remote : Hlc) (now : Nat) : Option Hlc :=
  if hDrift : remote.wallMs > now + driftLimitMs then
    none
  else
    mk? (recvWall local remote now) (recvCounter local remote now)

end Hlc

end CrdtBase
