import Batteries
import Init.Data.Ord.String

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

/-- Extended comparison including site ID for tiebreaking. -/
def compareWithSite (a b : Hlc × String) : Ordering :=
  if hPackLt : a.1.pack < b.1.pack then
    .lt
  else if hPackGt : b.1.pack < a.1.pack then
    .gt
  else if hSiteLt : a.2 < b.2 then
    .lt
  else if hSiteGt : b.2 < a.2 then
    .gt
  else
    .eq

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
def recvWall (localHlc remote : Hlc) (now : Nat) : Nat :=
  max3 localHlc.wallMs remote.wallMs now

/-- Compute the logical counter component for a recv. -/
def recvCounter (localHlc remote : Hlc) (now : Nat) : Nat :=
  let wall := recvWall localHlc remote now
  if hLocal : wall = localHlc.wallMs then
    if hRemote : wall = remote.wallMs then
      max localHlc.counter remote.counter + 1
    else
      localHlc.counter + 1
  else if hRemote : wall = remote.wallMs then
    remote.counter + 1
  else
    0

/-- Advance the local HLC based on a local event. -/
def now (localHlc : Hlc) (wall : Nat) : Option Hlc :=
  let wall' := max localHlc.wallMs wall
  let counter :=
    if wall' = localHlc.wallMs then
      localHlc.counter + 1
    else
      0
  mk? wall' counter

/-- Receive a remote HLC, rejecting on excessive clock drift. -/
def recv (localHlc remote : Hlc) (now : Nat) : Option Hlc :=
  if hDrift : remote.wallMs > now + driftLimitMs then
    none
  else
    mk? (recvWall localHlc remote now) (recvCounter localHlc remote now)

end Hlc

end CrdtBase
