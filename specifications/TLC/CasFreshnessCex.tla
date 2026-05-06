--------------------------- MODULE CasFreshnessCex ---------------------------
(* Minimal counterexample sketch: a state with `fp=1' and another cell      *)
(* already holding `1' can reach `cas' on the first probe without ever     *)
(* examining that cell.  Such a pre-state violates `CasProbeUniqueAbsFp'   *)
(* (now part of `CasFreshness' in OpenAddressing / the proof module).      *)
(* It is included here only to motivate the strengthening; it is *not* a    *)
(* reachable state of the full protocol under the proof invariants.       *)
EXTENDS Integers, Sequences

CONSTANT
  \* @type: Int;
  K,
  \* @type: Set(Int);
  fps,
  \* @type: Int;
  empty,
  \* @type: Set(Str);
  Writer,
  \* @type: Int;
  L

VARIABLE
  \* @type: Int -> Int;
  table,
  \* @type: Set(Int);
  history,
  \* @type: Str -> Str;
  pc,
  \* @type: Str -> Int;
  lo,
  \* @type: Str -> Int;
  fp,
  \* @type: Str -> Int;
  index,
  \* @type: Str -> Bool;
  result,
  \* @type: Str -> Int;
  exp

vars == << table, history, pc, lo, fp, index, result, exp >>

ProcSet == Writer

OAAssumption ==
  /\ K \in (Nat \ {0})
  /\ \A f \in fps : f \in (Nat \ {0})
  /\ empty \notin fps
  /\ L \in Nat
  /\ (2 * L) <= K

abs(number) == IF number < 0 THEN -1 * number ELSE number

mod(i, len) == IF i % len = 0 THEN len ELSE (i % len)

\* For the concrete constants below, the OpenAddressing idx formula reduces to
\* idx(f, p) = mod(3 * f + p, 4).  In particular, idx(1, 0) = 3.
idx(f, p) == mod(3 * f + p, 4)

insrt(self) ==
  /\ pc[self] = "insrt"
  /\ IF index[self] < L
        THEN /\ exp' =
                  [exp EXCEPT ![self] = table[idx(fp[self], index[self])]]
             /\ IF exp'[self] = empty \/
                   (exp'[self] < 0 /\ exp'[self] # (-1) * fp[self])
                   THEN /\ pc' = [pc EXCEPT ![self] = "cas"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "isMth"]
        ELSE /\ pc' = [pc EXCEPT ![self] = "tryEv"]
             /\ UNCHANGED exp
  /\ UNCHANGED << table, history, lo, fp, index, result >>

PickOrDone == {"pick", "Done"}

FpType == fp \in [Writer -> Int]

FpInFps ==
  \A self \in Writer :
    pc[self] \notin PickOrDone => fp[self] \in fps

PcRangeOK == TRUE

DoneImpliesAllSeen ==
  \A self \in ProcSet : pc[self] = "Done" => history = fps

Inv ==
  /\ history \subseteq fps
  /\ PcRangeOK
  /\ FpType
  /\ FpInFps
  /\ DoneImpliesAllSeen

ResultType == result \in [ProcSet -> BOOLEAN]

\* Strengthened probe hygiene (mirrors OpenAddressing.tla `CasProbeUniqueAbsFp').
CasProbeUniqueAbsFp ==
  \A self \in Writer :
    pc[self] \in {"insrt", "cas"} =>
      \A k \in 1..K :
        /\ table[k] # empty
        /\ abs(table[k]) = abs(fp[self])
        => k = idx(fp[self], index[self])

CasFreshnessCore ==
  \A self \in Writer :
    pc[self] = "cas" /\
    table[idx(fp[self], index[self])] = exp[self] =>
      /\ idx(fp[self], index[self]) \in 1..K
      /\ \A k \in 1..K :
           k # idx(fp[self], index[self]) /\ table[k] # empty =>
             abs(table[k]) # abs(fp[self])
      /\ \A s2 \in Writer :
           pc[s2] \in {"nestedIns", "set"} /\ lo[s2] # empty =>
             abs(lo[s2]) # abs(fp[self])

CasFreshness == CasProbeUniqueAbsFp /\ CasFreshnessCore

CexConstants ==
  /\ K = 4
  /\ L = 1
  /\ fps = {1, 2}
  /\ empty = 0
  /\ Writer = {"w"}

CexState ==
  /\ table = [i \in 1..4 |-> IF i = 1 THEN 1 ELSE 0]
  /\ history = {}
  /\ lo = [self \in {"w"} |-> 0]
  /\ fp = [self \in {"w"} |-> 1]
  /\ index = [self \in {"w"} |-> 0]
  /\ result = [self \in {"w"} |-> FALSE]
  /\ exp = [self \in {"w"} |-> -1]
  /\ pc = [self \in {"w"} |-> "insrt"]

CexInit ==
  /\ CexConstants
  /\ CexState
  /\ OAAssumption
  /\ Inv
  /\ ResultType
  (* `CasProbeUniqueAbsFp' is false here on purpose; do not conjoin full    *)
  (* `CasFreshness' from OpenAddressing onto this artificial pre-state.       *)

CexNext == insrt("w")

=============================================================================
