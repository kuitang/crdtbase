set_option autoImplicit false

namespace CrdtBase

namespace Replication

structure LogEntry where
  siteId : String
  seq : Nat
  deriving DecidableEq, Repr

def stringLt (a b : String) : Bool :=
  match compare a b with
  | .lt => true
  | _ => false

def insertSiteId (siteId : String) : List String → List String
  | [] => [siteId]
  | head :: tail =>
      if siteId = head then
        head :: tail
      else if stringLt siteId head then
        siteId :: head :: tail
      else
        head :: insertSiteId siteId tail

def listSites (entries : List LogEntry) : List String :=
  entries.foldl (fun sites entry => insertSiteId entry.siteId sites) []

def insertSeq (seq : Nat) : List Nat → List Nat
  | [] => [seq]
  | head :: tail =>
      if seq = head then
        head :: tail
      else if seq < head then
        seq :: head :: tail
      else
        head :: insertSeq seq tail

def canonicalSeqs (entries : List LogEntry) (siteId : String) : List Nat :=
  entries.foldl
    (fun seqs entry => if entry.siteId = siteId then insertSeq entry.seq seqs else seqs)
    []

def getHead (entries : List LogEntry) (siteId : String) : Nat :=
  (canonicalSeqs entries siteId).foldl Nat.max 0

def takeContiguousFrom (expected : Nat) : List Nat → List Nat
  | [] => []
  | seq :: tail =>
      if seq = expected then
        seq :: takeContiguousFrom (expected + 1) tail
      else
        []

def readSince (entries : List LogEntry) (siteId : String) (since : Nat) : List Nat :=
  let seqs := (canonicalSeqs entries siteId).filter (fun seq => seq > since)
  takeContiguousFrom (since + 1) seqs

end Replication

end CrdtBase
