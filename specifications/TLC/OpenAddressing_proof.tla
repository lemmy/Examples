--------------------------- MODULE OpenAddressing_proof ---------------------------
(***************************************************************************)
(* Proofs checked by TLAPS about the OpenAddressing PlusCal specification. *)
(*                                                                         *)
(* The OpenAddressing module specifies a concurrent, open-addressing       *)
(* fingerprint hash table with eviction to external storage (the Java      *)
(* OffHeapDiskFPSet algorithm).  Several safety properties are stated in   *)
(* the spec:                                                               *)
(*                                                                         *)
(*   Contains, Duplicates, Sorted, Consistent, CompleteAsSafety            *)
(*                                                                         *)
(* `Contains', `Duplicates', `Sorted', and `Consistent' are all very deep  *)
(* properties about the concurrent insertion/eviction algorithm; their     *)
(* TLAPS proofs would require sequence-level reasoning over `SelectSeq',   *)
(* sortedness invariants, and the algebraic properties of the hashing      *)
(* operators (`mod', `rescale', `idx').  We leave their full inductive     *)
(* proofs as OMITTED stubs (with the recommended invariant chain stated),  *)
(* and concentrate on what is fully tractable in this round:               *)
(*                                                                         *)
(*   THEOREM CompleteSafety  == Spec => []CompleteAsSafety                 *)
(*                                                                         *)
(* That property captures the partial-correctness statement that whenever  *)
(* a writer process reaches its `Done' label, all fingerprints in `fps'    *)
(* have actually been observed in the `history' set.  It is implied by a   *)
(* small inductive invariant `Inv' that we discharge in full.              *)
(***************************************************************************)
EXTENDS OpenAddressing, TLAPS, SequenceTheorems

(***************************************************************************)
(* The set of pc labels that appear in the spec.  The PlusCal translation  *)
(* uses string labels at every control point of `p(self)' and the          *)
(* `Evict(self)' procedure (plus the implicit `Done' label injected by the *)
(* translator for terminating processes).                                  *)
(***************************************************************************)
EvictLabels  == {"strIns", "nestedIns", "set", "flush", "rtrn"}
WriterLabels == {"pick", "put", "waitEv", "endWEv", "chkSnc", "cntns",
                 "onSnc", "insrt", "isMth", "cas", "tryEv", "waitIns",
                 "endEv", "Done"}
PcRange      == WriterLabels \cup EvictLabels

(***************************************************************************)
(* `pick' and `Done' are the only pc values where `fp[self]' may legally   *)
(* hold its initial value (0) instead of an element of `fps':              *)
(*  - in the initial state every writer has pc = "pick" and fp = 0;        *)
(*  - the `pick' action either keeps pc = "pick" / sets pc = "Done"        *)
(*    (without picking an fp, because (fps \ history) = {}), or picks      *)
(*    f \in (fps \ history) and goes to "put".                             *)
(* For every other pc value, `fp[self]' must be in `fps' because the only  *)
(* path that reaches it goes through the `else' branch of `pick' which     *)
(* assigns fp[self] \in (fps \ history) \subseteq fps.                     *)
(***************************************************************************)
PickOrDone == {"pick", "Done"}

(***************************************************************************)
(* The inductive invariant.                                                *)
(*                                                                         *)
(*  - HistorySubset:  `history' is always a subset of `fps'.               *)
(*  - PcRangeOK:      every pc value is one of the labels in PcRange.      *)
(*  - FpInFps:        once a writer has left `pick' (and is not at `Done') *)
(*                    its in-flight fingerprint `fp[self]' is in `fps'.    *)
(*  - DoneImpliesAllSeen:  whenever a writer's pc is "Done", all of `fps'  *)
(*                    has been observed in `history'.                      *)
(***************************************************************************)
HistorySubset == history \subseteq fps

PcRangeOK == pc \in [ProcSet -> PcRange]

(***************************************************************************)
(* `fp' must always be a function from Writer to Int.  This is needed by   *)
(* TLAPS for the EXCEPT-semantics step `[fp EXCEPT ![self] = f][s2] = ...' *)
(* in the `pick' inductive case.                                           *)
(***************************************************************************)
FpType == fp \in [Writer -> Int]

FpInFps ==
  \A self \in Writer :
    pc[self] \notin PickOrDone => fp[self] \in fps

DoneImpliesAllSeen ==
  \A self \in ProcSet : pc[self] = "Done" => history = fps

(***************************************************************************)
(* Stack-shape invariant.                                                  *)
(*                                                                         *)
(* The PlusCal `call' construct pushes a frame onto `stack[self]' and      *)
(* `return' pops it.  In this spec, `Evict()' is `call'-ed only from       *)
(* `waitIns', which pushes a single frame whose saved `pc' is `"endEv"'    *)
(* (the writer's continuation after the procedure returns).  Hence:        *)
(*  - whenever a writer is anywhere inside the Evict body                  *)
(*    (`pc[self] \in EvictLabels'), `stack[self]' is exactly that          *)
(*    one-element sequence whose unique frame's saved `pc' is `"endEv"';   *)
(*  - whenever the writer is at any `WriterLabels' label (including        *)
(*    `"Done"'), `stack[self]' is the empty sequence.                      *)
(*                                                                         *)
(* This is what lets us conclude in the `rtrn' case that                   *)
(* `pc'[self] = Head(stack[self]).pc = "endEv" \in PcRange' and that       *)
(* `stack'[self] = Tail(<<frame>>) = <<>>'.                                *)
(***************************************************************************)
StackOK ==
  /\ DOMAIN stack = ProcSet
  /\ \A self \in ProcSet :
       /\ pc[self] \in EvictLabels =>
            /\ stack[self] # <<>>
            /\ Tail(stack[self]) = <<>>
            /\ Head(stack[self]).pc = "endEv"
       /\ pc[self] \in WriterLabels => stack[self] = <<>>

Inv ==
  /\ HistorySubset
  /\ PcRangeOK
  /\ FpType
  /\ FpInFps
  /\ DoneImpliesAllSeen

(***************************************************************************)
(* Helper: ProcSet = Writer (the spec only declares writers as the set of  *)
(* fair processes; no readers are instantiated in this PlusCal version).   *)
(***************************************************************************)
LEMMA ProcSetIsWriter == ProcSet = Writer
  BY DEF ProcSet

(***************************************************************************)
(* Helper: every element of `fps' is an integer.  Discharged from the      *)
(* spec's ASSUME `\A fp \in fps : fp \in Nat \ {0}'.                       *)
(***************************************************************************)
LEMMA FpsAreInts == \A f \in fps : f \in Int
  <1>1. \A f \in fps : f \in Nat \ {0}
    BY OAAssumption
  <1>2. \A f \in fps : f \in Nat
    BY <1>1
  <1>. QED  BY <1>2

(***************************************************************************)
(* Init implies Inv.                                                       *)
(***************************************************************************)
LEMMA InitInv == Init => Inv
  <1>. SUFFICES ASSUME Init  PROVE Inv
    OBVIOUS
  <1>1. HistorySubset
    BY DEF Init, HistorySubset
  <1>2. PcRangeOK
    <2>1. pc = [self \in ProcSet |-> "pick"]
      BY DEF Init
    <2>2. "pick" \in PcRange
      BY DEF PcRange, WriterLabels
    <2>. QED  BY <2>1, <2>2 DEF PcRangeOK
  <1>3. FpType
    <2>1. fp = [self \in Writer |-> 0]
      BY DEF Init
    <2>2. \A self \in Writer : (0 \in Int)
      OBVIOUS
    <2>. QED  BY <2>1, <2>2 DEF FpType
  <1>4. FpInFps
    \* Every writer has pc[self] = "pick" \in PickOrDone, so the implication
    \* is vacuously true.
    <2>. SUFFICES ASSUME NEW self \in Writer,
                         pc[self] \notin PickOrDone
                  PROVE  fp[self] \in fps
      BY DEF FpInFps
    <2>1. pc[self] = "pick"
      BY ProcSetIsWriter DEF Init
    <2>2. "pick" \in PickOrDone
      BY DEF PickOrDone
    <2>. QED  BY <2>1, <2>2
  <1>5. DoneImpliesAllSeen
    \* Initially pc[self] = "pick" /= "Done" for every self, so vacuous.
    <2>. SUFFICES ASSUME NEW self \in ProcSet, pc[self] = "Done"
                  PROVE  history = fps
      BY DEF DoneImpliesAllSeen
    <2>1. pc[self] = "pick"
      BY DEF Init
    <2>. QED  BY <2>1
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(***************************************************************************)
(* Init implies StackOK.  Every writer starts at "pick" with an empty      *)
(* stack, so the EvictLabels conjunct is vacuously true and the            *)
(* WriterLabels conjunct is witnessed directly by the initial value.       *)
(***************************************************************************)
LEMMA InitStackOK == Init => StackOK
  <1>. SUFFICES ASSUME Init  PROVE StackOK
    OBVIOUS
  <1>0. DOMAIN stack = ProcSet
    BY DEF Init
  <1>. SUFFICES ASSUME NEW self \in ProcSet
                PROVE  /\ pc[self] \in EvictLabels =>
                            /\ stack[self] # <<>>
                            /\ Tail(stack[self]) = <<>>
                            /\ Head(stack[self]).pc = "endEv"
                       /\ pc[self] \in WriterLabels => stack[self] = <<>>
    BY <1>0 DEF StackOK
  <1>1. pc[self] = "pick"
    BY ProcSetIsWriter DEF Init
  <1>2. "pick" \notin EvictLabels
    BY DEF EvictLabels
  <1>3. stack[self] = <<>>
    BY ProcSetIsWriter DEF Init
  <1>. QED  BY <1>1, <1>2, <1>3

(***************************************************************************)
(* Inductive step for StackOK.                                             *)
(*                                                                         *)
(* `StackOK' is preserved by every action of `Next'.  The proof has the    *)
(* same case skeleton as `InvNext', but each case only has to show that    *)
(* the action neither (a) leaves a writer at an `EvictLabels' label with   *)
(* the wrong stack shape, nor (b) leaves a writer at a `WriterLabels'      *)
(* label with a non-empty stack.                                           *)
(*                                                                         *)
(* Most actions trivially preserve `StackOK' because they leave `stack'    *)
(* unchanged and only move `pc[self]' within the same label group          *)
(* (Evict labels stay Evict labels; Writer labels stay Writer labels).     *)
(* The two non-trivial actions are:                                        *)
(*   - `waitIns(self)': pushes the unique frame `[pc |-> "endEv", ...]'    *)
(*     onto the (then-empty) stack and moves `pc' from "waitIns" to        *)
(*     "strIns".                                                           *)
(*   - `rtrn(self)':    pops the (then unique) frame and moves `pc' from   *)
(*     "rtrn" to `Head(stack[self]).pc = "endEv"'.                         *)
(***************************************************************************)
(***************************************************************************)
(* Helper used in the inductive step of StackOKInd.  For any "boring"      *)
(* action -- one that leaves `stack' UNCHANGED, doesn't change `pc'        *)
(* outside `self', and keeps `pc[self]' inside the same label group --     *)
(* StackOK at any `s2 \in ProcSet' is preserved.  The hypotheses are       *)
(* per-s2 (rather than universally quantified over a fresh s) which lets   *)
(* the per-action discharges be one-liners over the action's UNCHANGED     *)
(* and EXCEPT clauses.                                                     *)
(***************************************************************************)
LEMMA StackOK_BoringEvict ==
  ASSUME StackOK,
         NEW self \in ProcSet,
         NEW s2 \in ProcSet,
         stack' = stack,
         s2 # self => pc'[s2] = pc[s2],
         pc[self] \in EvictLabels,
         pc'[self] \in EvictLabels
  PROVE  /\ pc'[s2] \in EvictLabels =>
              /\ stack'[s2] # <<>>
              /\ Tail(stack'[s2]) = <<>>
              /\ Head(stack'[s2]).pc = "endEv"
         /\ pc'[s2] \in WriterLabels => stack'[s2] = <<>>
  <1>. USE DEF StackOK, EvictLabels, WriterLabels, ProcSet
  <1>1. CASE s2 = self
    <2>1. /\ stack[self] # <<>>
          /\ Tail(stack[self]) = <<>>
          /\ Head(stack[self]).pc = "endEv"
      BY DEF StackOK
    <2>2. /\ stack'[s2] # <<>>
          /\ Tail(stack'[s2]) = <<>>
          /\ Head(stack'[s2]).pc = "endEv"
      BY <1>1, <2>1
    <2>3. pc'[s2] \in EvictLabels  BY <1>1
    <2>4. pc'[s2] \notin WriterLabels  BY <2>3
    <2>. QED  BY <2>2, <2>3, <2>4
  <1>2. CASE s2 # self
    <2>1. pc'[s2] = pc[s2]  BY <1>2
    <2>2. stack'[s2] = stack[s2]  OBVIOUS
    <2>. QED  BY <2>1, <2>2 DEF StackOK
  <1>. QED  BY <1>1, <1>2

LEMMA StackOK_BoringWriter ==
  ASSUME StackOK,
         NEW self \in ProcSet,
         NEW s2 \in ProcSet,
         stack' = stack,
         s2 # self => pc'[s2] = pc[s2],
         pc[self] \in WriterLabels,
         pc'[self] \in WriterLabels
  PROVE  /\ pc'[s2] \in EvictLabels =>
              /\ stack'[s2] # <<>>
              /\ Tail(stack'[s2]) = <<>>
              /\ Head(stack'[s2]).pc = "endEv"
         /\ pc'[s2] \in WriterLabels => stack'[s2] = <<>>
  <1>. USE DEF StackOK, EvictLabels, WriterLabels, ProcSet
  <1>1. CASE s2 = self
    <2>1. stack[self] = <<>>  BY DEF StackOK
    <2>2. stack'[s2] = <<>>  BY <1>1, <2>1
    <2>3. pc'[s2] \in WriterLabels  BY <1>1
    <2>4. pc'[s2] \notin EvictLabels  BY <2>3
    <2>. QED  BY <2>2, <2>3, <2>4
  <1>2. CASE s2 # self
    <2>1. pc'[s2] = pc[s2]  BY <1>2
    <2>2. stack'[s2] = stack[s2]  OBVIOUS
    <2>. QED  BY <2>1, <2>2 DEF StackOK
  <1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Helper lemma: extract `stack' = stack' from `UNCHANGED vars'.  TLAPS'   *)
(* SMT backends do not reliably project a 15-tuple equality down to a      *)
(* single component, so this is proved standalone with the Isabelle        *)
(* backend (which handles tuple destructuring directly).                   *)
(***************************************************************************)
LEMMA UnchangedVarsImpliesUnchangedStack ==
  ASSUME UNCHANGED vars
  PROVE  stack' = stack
  <1>1. <<table, external, newexternal, evict, waitCnt, history,
         pc, stack, ei, ej, lo, fp, index, result, expected>>'
        =
        <<table, external, newexternal, evict, waitCnt, history,
         pc, stack, ei, ej, lo, fp, index, result, expected>>
    BY DEF vars
  <1>. QED  BY <1>1

LEMMA StackOKInd == Inv /\ StackOK /\ [Next]_vars => StackOK'
  <1>. SUFFICES ASSUME Inv, StackOK, [Next]_vars  PROVE StackOK'
    OBVIOUS
  <1>. USE DEF Inv, PcRangeOK, PcRange, StackOK,
              EvictLabels, WriterLabels, ProcSet
  <1>0. DOMAIN stack = ProcSet
    BY DEF StackOK
  <1>00. ASSUME UNCHANGED vars
         PROVE  DOMAIN stack' = ProcSet
    <2>. USE <1>00
    <2>1. stack' = stack  BY UnchangedVarsImpliesUnchangedStack
    <2>. QED  BY <1>0, <2>1
  <1>01. ASSUME NEW self \in ProcSet, Evict(self)
         PROVE  DOMAIN stack' = ProcSet
    <2>. USE <1>01
    <2>1. CASE strIns(self)  BY <1>0, <2>1 DEF strIns
    <2>2. CASE nestedIns(self)  BY <1>0, <2>2 DEF nestedIns
    <2>3. CASE set(self)  BY <1>0, <2>3 DEF set
    <2>4. CASE flush(self)  BY <1>0, <2>4 DEF flush
    <2>5. CASE rtrn(self)  BY <1>0, <2>5 DEF rtrn
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Evict
  <1>02. ASSUME NEW self \in Writer, p(self)
         PROVE  DOMAIN stack' = ProcSet
    <2>. USE <1>02
    <2>0. self \in ProcSet  BY ProcSetIsWriter
    <2>1. CASE pick(self)  BY <1>0, <2>1 DEF pick
    <2>2. CASE put(self)  BY <1>0, <2>2 DEF put
    <2>3. CASE waitEv(self)  BY <1>0, <2>3 DEF waitEv
    <2>4. CASE endWEv(self)  BY <1>0, <2>4 DEF endWEv
    <2>5. CASE chkSnc(self)  BY <1>0, <2>5 DEF chkSnc
    <2>6. CASE cntns(self)  BY <1>0, <2>6 DEF cntns
    <2>7. CASE onSnc(self)  BY <1>0, <2>7 DEF onSnc
    <2>8. CASE insrt(self)  BY <1>0, <2>8 DEF insrt
    <2>9. CASE isMth(self)  BY <1>0, <2>9 DEF isMth
    <2>10. CASE cas(self)  BY <1>0, <2>10 DEF cas
    <2>11. CASE tryEv(self)  BY <1>0, <2>11 DEF tryEv
    <2>12. CASE waitIns(self)  BY <1>0, <2>0, <2>12 DEF waitIns
    <2>13. CASE endEv(self)  BY <1>0, <2>13 DEF endEv
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
                  <2>8, <2>9, <2>10, <2>11, <2>12, <2>13 DEF p
  <1>03. CASE Terminating
    BY <1>0, <1>03 DEF Terminating, vars
  <1>04. DOMAIN stack' = ProcSet
    BY <1>00, <1>01, <1>02, <1>03 DEF Next
  <1>. SUFFICES ASSUME NEW s2 \in ProcSet
                PROVE  /\ pc'[s2] \in EvictLabels =>
                            /\ stack'[s2] # <<>>
                            /\ Tail(stack'[s2]) = <<>>
                            /\ Head(stack'[s2]).pc = "endEv"
                       /\ pc'[s2] \in WriterLabels => stack'[s2] = <<>>
    BY <1>04 DEF StackOK
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  /\ pc'[s2] \in EvictLabels =>
                    /\ stack'[s2] # <<>>
                    /\ Tail(stack'[s2]) = <<>>
                    /\ Head(stack'[s2]).pc = "endEv"
               /\ pc'[s2] \in WriterLabels => stack'[s2] = <<>>
    <2>1. CASE strIns(self)
      <3>a. stack' = stack          BY <2>1 DEF strIns
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>1 DEF strIns
      <3>c. pc[self] \in EvictLabels  BY <2>1 DEF strIns, EvictLabels
      <3>d. pc'[self] \in EvictLabels  BY <2>1 DEF strIns, EvictLabels
      <3>. QED  BY <3>a, <3>b, <3>c, <3>d, StackOK_BoringEvict
    <2>2. CASE nestedIns(self)
      <3>a. stack' = stack          BY <2>2 DEF nestedIns
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>2 DEF nestedIns
      <3>c. pc[self] \in EvictLabels  BY <2>2 DEF nestedIns, EvictLabels
      <3>d. pc'[self] \in EvictLabels  BY <2>2 DEF nestedIns, EvictLabels
      <3>. QED  BY <3>a, <3>b, <3>c, <3>d, StackOK_BoringEvict
    <2>3. CASE set(self)
      <3>a. stack' = stack          BY <2>3 DEF set
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>3 DEF set
      <3>c. pc[self] \in EvictLabels  BY <2>3 DEF set, EvictLabels
      <3>d. pc'[self] \in EvictLabels  BY <2>3 DEF set, EvictLabels
      <3>. QED  BY <3>a, <3>b, <3>c, <3>d, StackOK_BoringEvict
    <2>4. CASE flush(self)
      <3>a. stack' = stack          BY <2>4 DEF flush
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>4 DEF flush
      <3>c. pc[self] \in EvictLabels  BY <2>4 DEF flush, EvictLabels
      <3>d. pc'[self] \in EvictLabels  BY <2>4 DEF flush, EvictLabels
      <3>. QED  BY <3>a, <3>b, <3>c, <3>d, StackOK_BoringEvict
    <2>5. CASE rtrn(self)
      \* Pop the unique stack frame.  By StackOK at self (with pc[self] =
      \* "rtrn" \in EvictLabels), Tail(stack[self]) = <<>> and
      \* Head(stack[self]).pc = "endEv".  After the action,
      \* pc'[self] = Head(stack[self]).pc = "endEv" \in WriterLabels and
      \* stack'[self] = Tail(stack[self]) = <<>>.
      <3>. USE <2>5
      <3>0. /\ pc[self] = "rtrn"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
        BY DEF rtrn
      <3>1. /\ stack[self] # <<>>
            /\ Tail(stack[self]) = <<>>
            /\ Head(stack[self]).pc = "endEv"
        BY <3>0 DEF StackOK
      <3>2. pc'[self] = "endEv"
        BY <3>0, <3>1
      <3>3. stack'[self] = <<>>
        BY <3>0, <3>1
      <3>4. CASE s2 = self
        <4>1. pc'[s2] = "endEv"  BY <3>2, <3>4
        <4>2. pc'[s2] \in WriterLabels  BY <4>1
        <4>3. pc'[s2] \notin EvictLabels  BY <4>1
        <4>4. stack'[s2] = <<>>  BY <3>3, <3>4
        <4>. QED  BY <4>2, <4>3, <4>4
      <3>5. CASE s2 # self
        <4>1. pc'[s2] = pc[s2]  BY <3>0, <3>5
        <4>2. stack'[s2] = stack[s2]  BY <3>0, <3>5
        <4>. QED  BY <4>1, <4>2 DEF StackOK
      <3>. QED  BY <3>4, <3>5
    <2>. QED  BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Evict
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  /\ pc'[s2] \in EvictLabels =>
                    /\ stack'[s2] # <<>>
                    /\ Tail(stack'[s2]) = <<>>
                    /\ Head(stack'[s2]).pc = "endEv"
               /\ pc'[s2] \in WriterLabels => stack'[s2] = <<>>
    <2>0. self \in ProcSet  BY ProcSetIsWriter
    <2>1. CASE pick(self)
      <3>a. stack' = stack          BY <2>1 DEF pick
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>1 DEF pick
      <3>c. pc[self] \in WriterLabels  BY <2>1 DEF pick, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>1 DEF pick, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>2. CASE put(self)
      <3>a. stack' = stack          BY <2>2 DEF put
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>2 DEF put
      <3>c. pc[self] \in WriterLabels  BY <2>2 DEF put, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>2 DEF put, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>3. CASE waitEv(self)
      <3>a. stack' = stack          BY <2>3 DEF waitEv
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>3 DEF waitEv
      <3>c. pc[self] \in WriterLabels  BY <2>3 DEF waitEv, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>3 DEF waitEv, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>4. CASE endWEv(self)
      <3>a. stack' = stack          BY <2>4 DEF endWEv
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>4 DEF endWEv
      <3>c. pc[self] \in WriterLabels  BY <2>4 DEF endWEv, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>4 DEF endWEv, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>5. CASE chkSnc(self)
      <3>a. stack' = stack          BY <2>5 DEF chkSnc
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>5 DEF chkSnc
      <3>c. pc[self] \in WriterLabels  BY <2>5 DEF chkSnc, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>5 DEF chkSnc, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>6. CASE cntns(self)
      <3>a. stack' = stack          BY <2>6 DEF cntns
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>6 DEF cntns
      <3>c. pc[self] \in WriterLabels  BY <2>6 DEF cntns, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>6 DEF cntns, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>7. CASE onSnc(self)
      <3>a. stack' = stack          BY <2>7 DEF onSnc
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>7 DEF onSnc
      <3>c. pc[self] \in WriterLabels  BY <2>7 DEF onSnc, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>7 DEF onSnc, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>8. CASE insrt(self)
      <3>a. stack' = stack          BY <2>8 DEF insrt
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>8 DEF insrt
      <3>c. pc[self] \in WriterLabels  BY <2>8 DEF insrt, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>8 DEF insrt, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>9. CASE isMth(self)
      <3>a. stack' = stack          BY <2>9 DEF isMth
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>9 DEF isMth
      <3>c. pc[self] \in WriterLabels  BY <2>9 DEF isMth, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>9 DEF isMth, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>10. CASE cas(self)
      <3>a. stack' = stack          BY <2>10 DEF cas
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>10 DEF cas
      <3>c. pc[self] \in WriterLabels  BY <2>10 DEF cas, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>10 DEF cas, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>11. CASE tryEv(self)
      <3>a. stack' = stack          BY <2>11 DEF tryEv
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>11 DEF tryEv
      <3>c. pc[self] \in WriterLabels  BY <2>11 DEF tryEv, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>11 DEF tryEv, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>12. CASE waitIns(self)
      \* Push the (only) frame onto the empty stack.
      <3>. USE <2>12
      <3>0. /\ pc[self] = "waitIns"
            /\ \E frame :
                 /\ frame = [ procedure |-> "Evict",
                              pc        |-> "endEv",
                              ei        |-> ei[self],
                              ej        |-> ej[self],
                              lo        |-> lo[self] ]
                 /\ stack' = [stack EXCEPT ![self] = <<frame>> \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "strIns"]
        BY DEF waitIns
      <3>1. stack[self] = <<>>
        BY <3>0 DEF StackOK
      <3>2. PICK frame :
              /\ frame = [ procedure |-> "Evict",
                           pc        |-> "endEv",
                           ei        |-> ei[self],
                           ej        |-> ej[self],
                           lo        |-> lo[self] ]
              /\ stack' = [stack EXCEPT ![self] = <<frame>> \o stack[self]]
        BY <3>0
      <3>3. stack'[self] = <<frame>> \o stack[self]
        BY <3>2
      <3>4. <<frame>> \in Seq({frame})
        BY IsASeq
      <3>5. <<frame>> \o <<>> = <<frame>>
        BY <3>4, ConcatEmptySeq
      <3>6. stack'[self] = <<frame>>
        BY <3>1, <3>3, <3>5
      <3>7. <<frame>> # <<>>
        BY <3>4, EmptySeq
      <3>8. Tail(<<frame>>) = <<>>
        <4>1. <<frame>> # <<>>  BY <3>7
        <4>2. Tail(<<frame>>) = SubSeq(<<frame>>, 2, Len(<<frame>>))
          BY <3>4, <4>1, TailIsSubSeq
        <4>3. Len(<<frame>>) = 1
          BY <3>4, IsASeq
        <4>4. Tail(<<frame>>) = SubSeq(<<frame>>, 2, 1)
          BY <4>2, <4>3
        <4>5. SubSeq(<<frame>>, 2, 1) = <<>>
          BY SubSeqEmpty
        <4>. QED  BY <4>4, <4>5
      <3>9. Head(<<frame>>) = frame
        BY DEF Head
      <3>10. frame.pc = "endEv"
        BY <3>2
      <3>11. pc'[self] = "strIns"
        BY <3>0
      <3>12. CASE s2 = self
        <4>1. pc'[s2] = "strIns"  BY <3>11, <3>12
        <4>2. pc'[s2] \in EvictLabels  BY <4>1
        <4>3. pc'[s2] \notin WriterLabels  BY <4>2
        <4>4. stack'[s2] = <<frame>>  BY <3>6, <3>12
        <4>5. stack'[s2] # <<>>  BY <4>4, <3>7
        <4>6. Tail(stack'[s2]) = <<>>  BY <4>4, <3>8
        <4>7. Head(stack'[s2]).pc = "endEv"  BY <4>4, <3>9, <3>10
        <4>. QED  BY <4>2, <4>3, <4>5, <4>6, <4>7
      <3>13. CASE s2 # self
        <4>1. pc'[s2] = pc[s2]  BY <3>0, <3>13
        <4>2. stack'[s2] = stack[s2]  BY <3>2, <3>13
        <4>. QED  BY <4>1, <4>2 DEF StackOK
      <3>. QED  BY <3>12, <3>13
    <2>13. CASE endEv(self)
      <3>a. stack' = stack          BY <2>13 DEF endEv
      <3>b. s2 # self => pc'[s2] = pc[s2]  BY <2>13 DEF endEv
      <3>c. pc[self] \in WriterLabels  BY <2>13 DEF endEv, WriterLabels
      <3>d. pc'[self] \in WriterLabels  BY <2>13 DEF endEv, WriterLabels
      <3>. QED  BY <2>0, <3>a, <3>b, <3>c, <3>d, StackOK_BoringWriter
    <2>. QED  BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
                  <2>8, <2>9, <2>10, <2>11, <2>12, <2>13 DEF p
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* Helper used in the inductive step: under `Inv', any successful `cas'    *)
(* by self only adds `fp[self] \in fps' to `history'.                      *)
(***************************************************************************)
LEMMA CasFpInFps ==
  ASSUME Inv,
         NEW self \in Writer,
         pc[self] = "cas"
  PROVE  fp[self] \in fps
  <1>. "cas" \notin PickOrDone
    BY DEF PickOrDone
  <1>. QED  BY DEF Inv, FpInFps

(***************************************************************************)
(* Inductive step.                                                         *)
(*                                                                         *)
(* The proof proceeds by case analysis on which top-level action of the    *)
(* spec's `Next' fired (Evict procedure body, writer body, or stutter).    *)
(* Within each `p(self)' case the writer's pc determines the disjunct.     *)
(***************************************************************************)
LEMMA InvNext == Inv /\ StackOK /\ [Next]_vars => Inv'
  <1>. SUFFICES ASSUME Inv, StackOK, [Next]_vars  PROVE Inv'
    OBVIOUS
  <1>. USE DEF Inv, HistorySubset, PcRangeOK, FpType, FpInFps,
              DoneImpliesAllSeen, StackOK,
              PcRange, WriterLabels, EvictLabels, PickOrDone, ProcSet
  (***********************************************************************)
  (* Stutter: vars unchanged => Inv unchanged.                            *)
  (***********************************************************************)
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  (***********************************************************************)
  (* Evict procedure disjuncts (called only by writers; `fp', `index',    *)
  (* `result', `expected', `history' are all UNCHANGED).                  *)
  (***********************************************************************)
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  Inv'
    <2>1. CASE strIns(self)
      BY <2>1 DEF strIns
    <2>2. CASE nestedIns(self)
      BY <2>2 DEF nestedIns
    <2>3. CASE set(self)
      BY <2>3 DEF set
    <2>4. CASE flush(self)
      BY <2>4 DEF flush
    <2>5. CASE rtrn(self)
      \* Returning Evict pops the unique stack frame and restores
      \* pc'[self] = Head(stack[self]).pc.  By StackOK at self (with
      \* pc[self] = "rtrn" \in EvictLabels) we know
      \*   Head(stack[self]).pc = "endEv",
      \* hence pc'[self] = "endEv".  The other invariants then follow
      \* because:
      \*   - history, fp, table, external, ... are all UNCHANGED;
      \*   - pc'[self] = "endEv" \in PcRange and \notin PickOrDone (so
      \*     FpInFps' for self holds because fp[self] is already in fps
      \*     by FpInFps with pc[self] = "rtrn" \notin PickOrDone);
      \*   - "endEv" /= "Done" so DoneImpliesAllSeen' is vacuous for self.
      <3>. USE <2>5 DEF rtrn
      <3>1. pc[self] = "rtrn"  OBVIOUS
      <3>2. /\ stack[self] # <<>>
            /\ Head(stack[self]).pc = "endEv"
        BY <3>1 DEF StackOK
      <3>3. pc'[self] = Head(stack[self]).pc
        OBVIOUS
      <3>4. pc'[self] = "endEv"
        BY <3>2, <3>3
      <3>5. history' = history  OBVIOUS
      <3>6. fp' = fp  OBVIOUS
      <3>7. HistorySubset'  BY <3>5
      <3>8. PcRangeOK'
        \* For self, pc'[self] = "endEv" \in PcRange.  For s2 # self,
        \* pc'[s2] = pc[s2] \in PcRange by Inv.
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet
                      PROVE  pc'[s2] \in PcRange
          BY DEF PcRangeOK
        <4>1. CASE s2 = self
          <5>1. pc'[s2] = "endEv"  BY <3>4, <4>1
          <5>. QED  BY <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>9. FpType'  BY <3>6
      <3>10. FpInFps'
        \* fp unchanged.  For self, by FpInFps and pc[self] = "rtrn"
        \* \notin PickOrDone, fp[self] \in fps; pc'[self] = "endEv"
        \* \notin PickOrDone, so we still need fp'[self] = fp[self] \in fps.
        <4>. SUFFICES ASSUME NEW s2 \in Writer,
                              pc'[s2] \notin PickOrDone
                      PROVE  fp'[s2] \in fps
          BY DEF FpInFps
        <4>1. fp'[s2] = fp[s2]  BY <3>6
        <4>2. CASE s2 = self
          <5>1. pc[self] = "rtrn"  BY <3>1
          <5>2. "rtrn" \notin PickOrDone  OBVIOUS
          <5>3. fp[self] \in fps  BY <5>1, <5>2
          <5>. QED  BY <4>1, <4>2, <5>3
        <4>3. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>3
          <5>2. pc[s2] \notin PickOrDone  BY <5>1
          <5>3. fp[s2] \in fps  BY <5>2
          <5>. QED  BY <4>1, <5>3
        <4>. QED  BY <4>2, <4>3
      <3>11. DoneImpliesAllSeen'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                      PROVE  history' = fps
          BY DEF DoneImpliesAllSeen
        <4>1. s2 # self
          \* pc'[self] = "endEv" /= "Done".
          BY <3>4
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] = "Done"  BY <4>2
        <4>4. history = fps  BY <4>3
        <4>. QED  BY <3>5, <4>4
      <3>. QED  BY <3>7, <3>8, <3>9, <3>10, <3>11
    <2>. QED  BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Evict
  (***********************************************************************)
  (* Writer body disjuncts.                                               *)
  (***********************************************************************)
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  Inv'
    <2>1. CASE pick(self)
      <3>. USE <2>1 DEF pick
      <3>1. CASE (fps \ history) = {}
        \* Then pc'[self] = "Done" and history' = history.  We must show
        \* history = fps here.
        <4>1. history \subseteq fps
          OBVIOUS
        <4>2. fps \ history = {}
          BY <3>1
        <4>3. history = fps
          BY <4>1, <4>2
        <4>4. pc' = [pc EXCEPT ![self] = "Done"]
          BY <3>1
        <4>5. fp' = fp
          BY <3>1
        <4>6. history' = history
          OBVIOUS
        <4>7. HistorySubset'
          BY <4>3, <4>6
        <4>8. PcRangeOK'
          <5>1. "Done" \in PcRange  OBVIOUS
          <5>. QED  BY <4>4, <5>1
        <4>FpType. FpType'
          BY <4>5
        <4>9. FpInFps'
          \* fp unchanged.  For self, pc' = "Done" => premise FALSE.
          \* For other writers, pc' = pc, fp' = fp, invariant by Inv.
          <5>. SUFFICES ASSUME NEW s2 \in Writer, pc'[s2] \notin PickOrDone
                        PROVE  fp'[s2] \in fps
            OBVIOUS
          <5>1. CASE s2 = self
            <6>1. pc'[s2] = "Done"  BY <4>4, <5>1
            <6>. QED  BY <6>1
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <4>4, <5>2
            <6>2. fp'[s2] = fp[s2]  BY <4>5
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <5>1, <5>2
        <4>10. DoneImpliesAllSeen'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                        PROVE  history' = fps
            OBVIOUS
          <5>1. CASE s2 = self
            BY <4>3, <4>6, <5>1
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <4>4, <5>2
            <6>2. pc[s2] = "Done"  BY <6>1
            <6>3. history = fps  BY <6>2
            <6>. QED  BY <6>3, <4>6
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>7, <4>8, <4>FpType, <4>9, <4>10
      <3>2. CASE (fps \ history) # {}
        \* Else branch: pick f \in fps\history, set fp'[self] = f, pc' = "put".
        <4>1. PICK f \in (fps \ history) :
                /\ fp' = [fp EXCEPT ![self] = f]
                /\ pc' = [pc EXCEPT ![self] = "put"]
          BY <3>2
        <4>2. f \in fps
          BY <4>1
        <4>3. history' = history
          OBVIOUS
        <4>4. HistorySubset'
          BY <4>3
        <4>5. PcRangeOK'
          <5>1. "put" \in PcRange  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>FpType. FpType'
          \* fp' = [fp EXCEPT ![self] = f] is in [Writer -> Int] when
          \* fp \in [Writer -> Int] (FpType), self \in Writer, and f \in Int.
          <5>1. f \in Int
            <6>1. f \in fps  BY <4>2
            <6>. QED  BY <6>1, FpsAreInts
          <5>. QED  BY <4>1, <5>1
        <4>6. FpInFps'
          <5>. SUFFICES ASSUME NEW s2 \in Writer,
                                pc'[s2] \notin PickOrDone
                        PROVE  fp'[s2] \in fps
            OBVIOUS
          <5>1. CASE s2 = self
            <6>1. fp'[s2] = f  BY <4>1, <5>1
            <6>. QED  BY <4>2, <6>1
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <4>1, <5>2
            <6>2. fp'[s2] = fp[s2]  BY <4>1, <5>2
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <5>1, <5>2
        <4>7. DoneImpliesAllSeen'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                        PROVE  history' = fps
            OBVIOUS
          <5>1. s2 # self
            <6>1. pc'[self] = "put"  BY <4>1
            <6>. QED  BY <6>1
          <5>2. pc'[s2] = pc[s2]  BY <4>1, <5>1
          <5>3. pc[s2] = "Done"  BY <5>2
          <5>4. history = fps  BY <5>3
          <5>. QED  BY <5>4, <4>3
        <4>. QED  BY <4>4, <4>5, <4>FpType, <4>6, <4>7
      <3>. QED  BY <3>1, <3>2
    <2>2. CASE put(self)
      \* pc' goes to "waitEv" or "chkSnc", history unchanged, fp unchanged.
      \* Was self at "put" (in PickOrDone? no -- "put" \notin {pick, Done}),
      \* so by FpInFps fp[self] \in fps.  After the action, self moves to
      \* "waitEv" or "chkSnc", both \notin {pick, Done}, and fp[self]'
      \* still equals fp[self] \in fps.
      <3>. USE <2>2 DEF put
      <3>1. pc[self] = "put"
        OBVIOUS
      <3>2. "put" \notin PickOrDone
        OBVIOUS
      <3>3. fp[self] \in fps
        BY <3>1, <3>2
      <3>4. history' = history
        OBVIOUS
      <3>5. fp' = fp
        OBVIOUS
      <3>6. HistorySubset'
        BY <3>4
      <3>7. PcRangeOK'
        <4>1. "waitEv" \in PcRange /\ "chkSnc" \in PcRange  OBVIOUS
        <4>. QED  BY <4>1
      <3>8. FpInFps'
        <4>. SUFFICES ASSUME NEW s2 \in Writer,
                              pc'[s2] \notin PickOrDone
                      PROVE  fp'[s2] \in fps
          OBVIOUS
        <4>1. fp'[s2] = fp[s2]  BY <3>5
        <4>2. CASE s2 = self
          BY <4>1, <4>2, <3>3
        <4>3. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>3
          <5>. QED  BY <5>1, <4>1
        <4>. QED  BY <4>2, <4>3
      <3>9. DoneImpliesAllSeen'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                      PROVE  history' = fps
          OBVIOUS
        <4>1. s2 # self
          \* pc'[self] \in {"waitEv", "chkSnc"}, neither = "Done".
          OBVIOUS
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] = "Done"  BY <4>2
        <4>. QED  BY <4>3, <3>4
      <3>. QED  BY <3>6, <3>7, <3>8, <3>9
    <2>3. CASE waitEv(self)
      \* pc' = "endWEv", everything else unchanged.
      <3>. USE <2>3 DEF waitEv
      <3>1. "endWEv" \in PcRange  OBVIOUS
      <3>. QED  BY <3>1
    <2>4. CASE endWEv(self)
      \* pc' = "put", waitCnt' = waitCnt - 1, everything else unchanged.
      <3>. USE <2>4 DEF endWEv
      <3>1. "put" \in PcRange  OBVIOUS
      <3>. QED  BY <3>1
    <2>5. CASE chkSnc(self)
      <3>. USE <2>5 DEF chkSnc
      <3>1. "cntns" \in PcRange /\ "insrt" \in PcRange  OBVIOUS
      <3>. QED  BY <3>1
    <2>6. CASE cntns(self)
      <3>. USE <2>6 DEF cntns
      <3>1. "pick" \in PcRange /\ "onSnc" \in PcRange /\ "cntns" \in PcRange
        OBVIOUS
      <3>2. fp' = fp
        OBVIOUS
      <3>3. history' = history
        OBVIOUS
      <3>4. HistorySubset'  BY <3>3
      <3>5. PcRangeOK'  BY <3>1
      <3>6. FpInFps'
        <4>. SUFFICES ASSUME NEW s2 \in Writer,
                              pc'[s2] \notin PickOrDone
                      PROVE  fp'[s2] \in fps
          OBVIOUS
        <4>1. fp'[s2] = fp[s2]  BY <3>2
        <4>2. CASE s2 = self
          \* pc[self] = "cntns" \notin PickOrDone, so by Inv fp[self] \in fps.
          <5>1. pc[self] = "cntns" /\ "cntns" \notin PickOrDone
            OBVIOUS
          <5>2. fp[self] \in fps  BY <5>1
          <5>. QED  BY <4>1, <4>2, <5>2
        <4>3. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>3
          <5>. QED  BY <5>1, <4>1
        <4>. QED  BY <4>2, <4>3
      <3>7. DoneImpliesAllSeen'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                      PROVE  history' = fps
          OBVIOUS
        <4>1. s2 # self
          \* pc'[self] \in {"pick", "onSnc", "cntns"}, none = "Done".
          OBVIOUS
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] = "Done"  BY <4>2
        <4>. QED  BY <4>3, <3>3
      <3>. QED  BY <3>4, <3>5, <3>6, <3>7
    <2>7. CASE onSnc(self)
      <3>. USE <2>7 DEF onSnc
      <3>1. "pick" \in PcRange /\ "insrt" \in PcRange  OBVIOUS
      <3>2. fp' = fp
        OBVIOUS
      <3>3. history' = history
        OBVIOUS
      <3>4. HistorySubset'  BY <3>3
      <3>5. PcRangeOK'  BY <3>1
      <3>6. FpInFps'
        <4>. SUFFICES ASSUME NEW s2 \in Writer,
                              pc'[s2] \notin PickOrDone
                      PROVE  fp'[s2] \in fps
          OBVIOUS
        <4>1. fp'[s2] = fp[s2]  BY <3>2
        <4>2. CASE s2 = self
          <5>1. pc[self] = "onSnc" /\ "onSnc" \notin PickOrDone
            OBVIOUS
          <5>. QED  BY <4>1, <4>2, <5>1
        <4>3. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>3
          <5>. QED  BY <5>1, <4>1
        <4>. QED  BY <4>2, <4>3
      <3>7. DoneImpliesAllSeen'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                      PROVE  history' = fps
          OBVIOUS
        <4>1. s2 # self  OBVIOUS
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] = "Done"  BY <4>2
        <4>. QED  BY <4>3, <3>3
      <3>. QED  BY <3>4, <3>5, <3>6, <3>7
    <2>8. CASE insrt(self)
      <3>. USE <2>8 DEF insrt
      <3>1. "tryEv" \in PcRange /\ "cas" \in PcRange /\ "isMth" \in PcRange
        OBVIOUS
      <3>. QED  BY <3>1
    <2>9. CASE isMth(self)
      <3>. USE <2>9 DEF isMth
      <3>1. "pick" \in PcRange /\ "insrt" \in PcRange  OBVIOUS
      <3>2. fp' = fp
        OBVIOUS
      <3>3. history' = history
        OBVIOUS
      <3>4. HistorySubset'  BY <3>3
      <3>5. PcRangeOK'  BY <3>1
      <3>6. FpInFps'
        <4>. SUFFICES ASSUME NEW s2 \in Writer,
                              pc'[s2] \notin PickOrDone
                      PROVE  fp'[s2] \in fps
          OBVIOUS
        <4>1. fp'[s2] = fp[s2]  BY <3>2
        <4>2. CASE s2 = self
          <5>1. pc[self] = "isMth" /\ "isMth" \notin PickOrDone  OBVIOUS
          <5>. QED  BY <4>1, <4>2, <5>1
        <4>3. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>3
          <5>. QED  BY <5>1, <4>1
        <4>. QED  BY <4>2, <4>3
      <3>7. DoneImpliesAllSeen'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                      PROVE  history' = fps
          OBVIOUS
        <4>1. s2 # self  OBVIOUS
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] = "Done"  BY <4>2
        <4>. QED  BY <4>3, <3>3
      <3>. QED  BY <3>4, <3>5, <3>6, <3>7
    <2>10. CASE cas(self)
      \* This is the only writer disjunct that may grow `history`.
      <3>. USE <2>10 DEF cas
      <3>1. pc[self] = "cas"
        OBVIOUS
      <3>2. fp[self] \in fps
        BY <3>1, CasFpInFps
      <3>3. fp' = fp
        OBVIOUS
      <3>4. CASE result'[self]  \* successful cas: history grows by fp[self]
        <4>1. history' = history \cup {fp[self]}
          BY <3>4
        <4>2. pc' = [pc EXCEPT ![self] = "pick"]
          BY <3>4
        <4>3. HistorySubset'
          BY <3>2, <4>1
        <4>4. PcRangeOK'
          <5>1. "pick" \in PcRange  OBVIOUS
          <5>. QED  BY <4>2, <5>1
        <4>5. FpInFps'
          <5>. SUFFICES ASSUME NEW s2 \in Writer,
                                pc'[s2] \notin PickOrDone
                        PROVE  fp'[s2] \in fps
            OBVIOUS
          <5>1. fp'[s2] = fp[s2]  BY <3>3
          <5>2. CASE s2 = self
            <6>1. pc'[s2] = "pick"  BY <4>2, <5>2
            <6>2. "pick" \in PickOrDone  OBVIOUS
            <6>. QED  BY <6>1, <6>2
          <5>3. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <4>2, <5>3
            <6>. QED  BY <6>1, <5>1
          <5>. QED  BY <5>2, <5>3
        <4>6. DoneImpliesAllSeen'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                        PROVE  history' = fps
            OBVIOUS
          <5>1. s2 # self
            <6>1. pc'[self] = "pick"  BY <4>2
            <6>. QED  BY <6>1
          <5>2. pc'[s2] = pc[s2]  BY <4>2, <5>1
          <5>3. pc[s2] = "Done"  BY <5>2
          <5>4. history = fps  BY <5>3
          \* history' = history \cup {fp[self]} = fps \cup {fp[self]} = fps,
          \* because fp[self] \in fps.
          <5>5. fp[self] \in fps  BY <3>2
          <5>. QED  BY <4>1, <5>4, <5>5
        <4>. QED  BY <4>3, <4>4, <4>5, <4>6
      <3>5. CASE ~result'[self]  \* failed cas: history unchanged
        <4>1. history' = history
          BY <3>5
        <4>2. pc' = [pc EXCEPT ![self] = "insrt"]
          BY <3>5
        <4>3. HistorySubset'  BY <4>1
        <4>4. PcRangeOK'
          <5>1. "insrt" \in PcRange  OBVIOUS
          <5>. QED  BY <4>2, <5>1
        <4>5. FpInFps'
          <5>. SUFFICES ASSUME NEW s2 \in Writer,
                                pc'[s2] \notin PickOrDone
                        PROVE  fp'[s2] \in fps
            OBVIOUS
          <5>1. fp'[s2] = fp[s2]  BY <3>3
          <5>2. CASE s2 = self
            \* pc'[self] = "insrt" \notin PickOrDone; need fp[self] \in fps.
            BY <5>1, <5>2, <3>2
          <5>3. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <4>2, <5>3
            <6>. QED  BY <6>1, <5>1
          <5>. QED  BY <5>2, <5>3
        <4>6. DoneImpliesAllSeen'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "Done"
                        PROVE  history' = fps
            OBVIOUS
          <5>1. s2 # self
            <6>1. pc'[self] = "insrt"  BY <4>2
            <6>. QED  BY <6>1
          <5>2. pc'[s2] = pc[s2]  BY <4>2, <5>1
          <5>3. pc[s2] = "Done"  BY <5>2
          <5>4. history = fps  BY <5>3
          <5>. QED  BY <5>4, <4>1
        <4>. QED  BY <4>3, <4>4, <4>5, <4>6
      <3>. QED  BY <3>4, <3>5
    <2>11. CASE tryEv(self)
      <3>. USE <2>11 DEF tryEv
      <3>1. "waitIns" \in PcRange /\ "put" \in PcRange  OBVIOUS
      <3>. QED  BY <3>1
    <2>12. CASE waitIns(self)
      \* Procedure call: pc' goes to "strIns" (Evict's first label),
      \* and stack[self]' is pushed.  fp, history unchanged.
      <3>. USE <2>12 DEF waitIns
      <3>1. "strIns" \in PcRange  OBVIOUS
      <3>. QED  BY <3>1
    <2>13. CASE endEv(self)
      <3>. USE <2>13 DEF endEv
      <3>1. "put" \in PcRange  OBVIOUS
      <3>. QED  BY <3>1
    <2>. QED  BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
                  <2>8, <2>9, <2>10, <2>11, <2>12, <2>13 DEF p
  (***********************************************************************)
  (* Terminating disjunct: only enabled when every process is at "Done",  *)
  (* in which case Inv (in particular DoneImpliesAllSeen) is preserved    *)
  (* with vars unchanged.                                                 *)
  (***********************************************************************)
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* Main safety theorem: Spec implies CompleteAsSafety.                     *)
(***************************************************************************)
THEOREM CompleteSafety == Spec => []CompleteAsSafety
  <1>1. Inv => CompleteAsSafety
    BY DEF Inv, DoneImpliesAllSeen, CompleteAsSafety
  <1>2. Init => Inv /\ StackOK
    BY InitInv, InitStackOK
  <1>3. (Inv /\ StackOK) /\ [Next]_vars => (Inv /\ StackOK)'
    BY InvNext, StackOKInd
  <1>4. Spec => [](Inv /\ StackOK)
    BY <1>2, <1>3, PTL DEF Spec
  <1>. QED  BY <1>1, <1>4, PTL

(***************************************************************************)
(*                                                                         *)
(*  NO DUPLICATES IN THE TABLE OUTSIDE OF AN ACTIVE EVICTION.              *)
(*                                                                         *)
(*  We prove `Spec => []Duplicates' via a strengthened invariant `DupInv'  *)
(*  with three conjuncts:                                                  *)
(*                                                                         *)
(*    - TableType: every cell of `table' is in `fps \cup NegFps \cup       *)
(*      {empty}', where `NegFps = { -f : f \in fps }' covers the cells     *)
(*      marked for eviction by `flush'.                                    *)
(*                                                                         *)
(*    - FindOrPut => NoDupsTable: when `evict = FALSE', no two non-empty   *)
(*      cells of `table' have the same absolute value.  This is the        *)
(*      direct restatement of `Duplicates' on table indices.               *)
(*                                                                         *)
(*    - Post-flush pc invariant: whenever a writer is at `rtrn' or         *)
(*      `endEv' (the labels just before `evict' is cleared), the table     *)
(*      already satisfies `NoDupsTable'.  This is the only conjunct that   *)
(*      makes `FindOrPut => NoDupsTable' inductive at the `endEv'          *)
(*      transition, where `evict' flips from TRUE to FALSE.                *)
(*                                                                         *)
(*  The deep parts of the inductive step we leave as OMITTED:              *)
(*                                                                         *)
(*    (a) `cas' success branch (writer body): when the CAS atomically      *)
(*        writes `fp[self]' to `idx(fp[self], index[self])', preserving    *)
(*        no-duplicates requires that no other table position contains     *)
(*        `fp[self]' or `-fp[self]' beforehand.  This is the central       *)
(*        correctness property of the open-addressing probe sequence       *)
(*        plus the `cntns'/`isMth' check loop, requiring a per-process     *)
(*        invariant on the contents of `table' along the probe sequence    *)
(*        as a function of the algorithm's `index' / `expected' loop       *)
(*        variables.                                                       *)
(*                                                                         *)
(*    (b) The sort actions `nestedIns' (cell-shift) and `set' (cell-       *)
(*        place): these are the writer-Evict actions that mutate `table'   *)
(*        in non-`|.|'-preserving ways during the insertion-sort body.     *)
(*        They lie inside the Evict body (so `evict = TRUE' and the second *)
(*        conjunct is vacuous), but discharging their effect on the third  *)
(*        conjunct -- showing that no other writer is at `rtrn'/`endEv'    *)
(*        while we are mid-sort -- needs the procedure's mutual-exclusion  *)
(*        invariant (`waitCnt = Cardinality(Writer) - 1' when `Evict()' is *)
(*        active), which we do not formalise here.                         *)
(*                                                                         *)
(*    (c) `flush' loop exit (and entry to `rtrn'): at this point we need   *)
(*        `NoDupsTable' to hold, which requires carrying it across the     *)
(*        full sort+flush procedure.  The flush iterations only negate     *)
(*        cells (preserving `|table[i]|') so `NoDupsTable' is preserved    *)
(*        once established at flush entry; the genuinely deep step is      *)
(*        showing that the insertion sort permutes the multiset of         *)
(*        non-empty values in `table' (so `NoDupsTable' established        *)
(*        before sort entry survives sort exit).                           *)
(*                                                                         *)
(*  All other structural cases of the inductive step are fully discharged. *)
(***************************************************************************)
NegFps == { -f : f \in fps }
TableValues == fps \cup NegFps \cup {empty}
TableType == table \in [1..K -> TableValues]

NoDupsTable ==
  \A i, j \in 1..K :
    i # j /\ table[i] # empty /\ table[j] # empty
    => abs(table[i]) # abs(table[j])

DupInv ==
  /\ TableType
  /\ FindOrPut => NoDupsTable
  /\ \A self \in ProcSet : pc[self] \in {"rtrn", "endEv"} => NoDupsTable

(***************************************************************************)
(* Sequence-theoretic helper: when `t : 1..K -> TableValues' satisfies     *)
(* the per-index `NoDupsTable' property, `SelectSeq' filtering on `e #     *)
(* empty' yields a sequence whose entries all have distinct absolute       *)
(* values.                                                                 *)
(*                                                                         *)
(* As with the other `SelectSeq' lemmas earlier in this file, the proof    *)
(* requires recursive-function unfolding of `SelectSeq' that is not        *)
(* covered by TLAPS' standard library nor by `CommunityModules'.           *)
(***************************************************************************)
LEMMA SelectSeqAbsDistinct ==
  ASSUME NEW t \in [1..K -> TableValues],
         \A i, j \in 1..K : i # j /\ t[i] # empty /\ t[j] # empty
            => abs(t[i]) # abs(t[j])
  PROVE  LET sub == SelectSeq(t, LAMBDA e : e # empty)
         IN \A i \in 1..(Len(sub) - 1) :
              \A j \in (i+1)..Len(sub) :
                  abs(sub[i]) # abs(sub[j])
  OMITTED

(***************************************************************************)
(* Init implies DupInv.                                                    *)
(***************************************************************************)
LEMMA InitDupInv == Init => DupInv
  <1>. SUFFICES ASSUME Init  PROVE DupInv
    OBVIOUS
  <1>1. table = [i \in 1..K |-> empty]
    BY DEF Init
  <1>2. TableType
    <2>1. empty \in TableValues
      BY DEF TableValues
    <2>. QED  BY <1>1, <2>1 DEF TableType
  <1>3. FindOrPut => NoDupsTable
    <2>. SUFFICES ASSUME FindOrPut, NEW i \in 1..K, NEW j \in 1..K,
                         i # j, table[i] # empty, table[j] # empty
                  PROVE  abs(table[i]) # abs(table[j])
      BY DEF NoDupsTable
    <2>1. table[i] = empty
      BY <1>1
    <2>. QED  BY <2>1
  <1>4. \A self \in ProcSet : pc[self] \in {"rtrn", "endEv"} => NoDupsTable
    <2>. SUFFICES ASSUME NEW self \in ProcSet,
                         pc[self] \in {"rtrn", "endEv"}
                  PROVE  NoDupsTable
      OBVIOUS
    <2>1. pc[self] = "pick"
      BY DEF Init
    <2>. QED  BY <2>1
  <1>. QED  BY <1>2, <1>3, <1>4 DEF DupInv

(***************************************************************************)
(* Typing invariant: `result' is a Boolean-valued function on `ProcSet'.   *)
(*                                                                         *)
(* Init sets `result = [self \in Writer |-> FALSE]' and every action       *)
(* either leaves `result' UNCHANGED or writes a BOOLEAN at `self' via      *)
(* EXCEPT.  We state this as a separate invariant (not folded into `Inv')  *)
(* so that the existing `InvNext' proof is not perturbed; `DupInvNext'     *)
(* below threads it as an extra hypothesis, which unlocks the failed-CAS   *)
(* branch of `cas' (we need `result'[self] = FALSE' to identify the        *)
(* second IF's branch).                                                    *)
(***************************************************************************)
ResultType == result \in [ProcSet -> BOOLEAN]

LEMMA InitResultType == Init => ResultType
  <1>. SUFFICES ASSUME Init  PROVE ResultType
    OBVIOUS
  <1>1. result = [self \in Writer |-> FALSE]
    BY DEF Init
  <1>. QED  BY <1>1, ProcSetIsWriter DEF ResultType

LEMMA ResultTypeInd == ResultType /\ [Next]_vars => ResultType'
  <1>. SUFFICES ASSUME ResultType, [Next]_vars  PROVE ResultType'
    OBVIOUS
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF ResultType, vars
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  ResultType'
    \* All Evict sub-actions UNCHANGED result.
    <2>. USE <1>2 DEF Evict, strIns, nestedIns, set, flush, rtrn
    <2>1. result' = result
      OBVIOUS
    <2>. QED  BY <2>1 DEF ResultType
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  ResultType'
    <2>. USE <1>3, ProcSetIsWriter DEF p, ResultType
    <2>1. CASE pick(self)    BY <2>1  DEF pick
    <2>2. CASE put(self)
      \* put writes FALSE at self.
      <3>1. result' = [result EXCEPT ![self] = FALSE]
        BY <2>2 DEF put
      <3>. QED  BY <3>1
    <2>3. CASE waitEv(self)  BY <2>3  DEF waitEv
    <2>4. CASE endWEv(self)  BY <2>4  DEF endWEv
    <2>5. CASE chkSnc(self)  BY <2>5  DEF chkSnc
    <2>6. CASE cntns(self)   BY <2>6  DEF cntns
    <2>7. CASE onSnc(self)   BY <2>7  DEF onSnc
    <2>8. CASE isMth(self)   BY <2>8  DEF isMth
    <2>9. CASE insrt(self)   BY <2>9  DEF insrt
    <2>10. CASE cas(self)
      \* cas writes TRUE or FALSE at self.
      <3>1. CASE table[idx(fp[self],index[self])] = expected[self]
        <4>1. result' = [result EXCEPT ![self] = TRUE]
          BY <2>10, <3>1 DEF cas
        <4>. QED  BY <4>1
      <3>2. CASE ~(table[idx(fp[self],index[self])] = expected[self])
        <4>1. result' = [result EXCEPT ![self] = FALSE]
          BY <2>10, <3>2 DEF cas
        <4>. QED  BY <4>1
      <3>. QED  BY <3>1, <3>2
    <2>11. CASE tryEv(self)   BY <2>11 DEF tryEv
    <2>12. CASE waitIns(self) BY <2>12 DEF waitIns
    <2>13. CASE endEv(self)   BY <2>13 DEF endEv
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
                  <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars, ResultType
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* Typing invariant: `ei' is a Nat-valued function on `ProcSet', and any   *)
(* saved `ei' frame on a non-empty `stack' is also a Nat.  The second      *)
(* conjunct is necessary because `rtrn' pops `ei[self]' from the top of    *)
(* the stack; without it we could not conclude `ei'[self] \in Nat' after  *)
(* a return.                                                               *)
(*                                                                         *)
(* `EiType' is used to discharge `DupInvNext's flush inner-then branch,    *)
(* where we need `mod(ei[self], K) \in 1..K' -- a consequence of           *)
(* `ei[self] \in Nat' and `K \in Nat \ {0}' (OAAssumption).                *)
(***************************************************************************)
EiType ==
  /\ ei \in [ProcSet -> Nat]
  /\ DOMAIN lo = ProcSet
  /\ \A self \in ProcSet :
        stack[self] # <<>> => Head(stack[self]).ei \in Nat

LEMMA InitEiType == Init => EiType
  <1>. SUFFICES ASSUME Init  PROVE EiType
    OBVIOUS
  <1>1. ei = [self \in ProcSet |-> 1]
    BY DEF Init
  <1>2. ei \in [ProcSet -> Nat]
    BY <1>1 DEF EiType
  <1>3. \A self \in ProcSet : stack[self] = <<>>
    BY DEF Init
  <1>4. \A self \in ProcSet :
            stack[self] # <<>> => Head(stack[self]).ei \in Nat
    BY <1>3
  <1>5. lo = [self \in ProcSet |-> 0]
    BY DEF Init
  <1>6. DOMAIN lo = ProcSet
    BY <1>5
  <1>. QED  BY <1>2, <1>4, <1>6 DEF EiType

LEMMA EiTypeInd == StackOK /\ EiType /\ [Next]_vars => EiType'
  <1>. SUFFICES ASSUME StackOK, EiType, [Next]_vars  PROVE EiType'
    OBVIOUS
  <1>. USE DEF EiType, StackOK, EvictLabels, WriterLabels, ProcSet
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  EiType'
    <2>. USE <1>2 DEF Evict
    <2>1. CASE strIns(self)
      \* ei' = ei (inner-then) or ei' = [ei EXCEPT ![self] = 1] (inner-else);
      \* stack UNCHANGED.
      <3>. USE <2>1 DEF strIns
      <3>1. stack' = stack  OBVIOUS
      <3>2. CASE ei[self] <= K+L
        <4>1. ei' = ei  BY <3>2
        <4>. QED  BY <3>1, <4>1
      <3>3. CASE ~(ei[self] <= K+L)
        <4>1. ei' = [ei EXCEPT ![self] = 1]  BY <3>3
        <4>. QED  BY <3>1, <4>1
      <3>. QED  BY <3>2, <3>3
    <2>2. CASE nestedIns(self)
      \* ei, stack UNCHANGED.
      BY <2>2 DEF nestedIns
    <2>3. CASE set(self)
      \* ei' = [ei EXCEPT ![self] = ei[self] + 1]; stack UNCHANGED.
      <3>. USE <2>3 DEF set
      <3>1. stack' = stack  OBVIOUS
      <3>2. ei'[self] = ei[self] + 1
        OBVIOUS
      <3>3. ei[self] \in Nat
        OBVIOUS
      <3>4. \A s2 \in ProcSet : s2 # self => ei'[s2] = ei[s2]
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4
    <2>4. CASE flush(self)
      \* outer-then: ei' = [ei EXCEPT ![self] = ei[self] + 1];
      \* outer-else: ei, stack UNCHANGED.
      <3>. USE <2>4 DEF flush
      <3>1. stack' = stack  OBVIOUS
      <3>2. CASE ei[self] <= K+L
        <4>1. ei'[self] = ei[self] + 1
          BY <3>2
        <4>2. \A s2 \in ProcSet : s2 # self => ei'[s2] = ei[s2]
          BY <3>2
        <4>3. ei[self] \in Nat
          OBVIOUS
        <4>. QED  BY <3>1, <4>1, <4>2, <4>3
      <3>3. CASE ~(ei[self] <= K+L)
        <4>1. ei' = ei  BY <3>3
        <4>. QED  BY <3>1, <4>1
      <3>. QED  BY <3>2, <3>3
    <2>5. CASE rtrn(self)
      \* Pops stack; ei'[self] = Head(stack[self]).ei.
      <3>. USE <2>5 DEF rtrn
      <3>1. pc[self] = "rtrn"
        OBVIOUS
      <3>2. pc[self] \in EvictLabels
        BY <3>1
      <3>3. stack[self] # <<>>
        BY <3>2
      <3>4. Head(stack[self]).ei \in Nat
        BY <3>3
      <3>5. ei'[self] = Head(stack[self]).ei
        OBVIOUS
      <3>6. ei'[self] \in Nat
        BY <3>4, <3>5
      <3>7. \A s2 \in ProcSet : s2 # self => ei'[s2] = ei[s2]
        OBVIOUS
      <3>8. ei' \in [ProcSet -> Nat]
        BY <3>6, <3>7
      \* Post-state stack: Tail at self, unchanged at others.  By StackOK
      \* the pre-state stack[self] has exactly one frame, so the tail is
      \* empty and the second conjunct is vacuous at self.
      <3>9. stack'[self] = Tail(stack[self])
        OBVIOUS
      <3>10. Tail(stack[self]) = <<>>
        BY <3>2
      <3>11. stack'[self] = <<>>
        BY <3>9, <3>10
      <3>12. \A s2 \in ProcSet :
                stack'[s2] # <<>> => Head(stack'[s2]).ei \in Nat
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, stack'[s2] # <<>>
                      PROVE  Head(stack'[s2]).ei \in Nat
          OBVIOUS
        <4>1. CASE s2 = self
          BY <3>11, <4>1
        <4>2. CASE s2 # self
          <5>1. stack'[s2] = stack[s2]
            BY <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>8, <3>12
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  EiType'
    <2>. USE <1>3, ProcSetIsWriter DEF p
    <2>1. CASE pick(self)      BY <2>1 DEF pick
    <2>2. CASE put(self)       BY <2>2 DEF put
    <2>3. CASE waitEv(self)    BY <2>3 DEF waitEv
    <2>4. CASE endWEv(self)    BY <2>4 DEF endWEv
    <2>5. CASE chkSnc(self)    BY <2>5 DEF chkSnc
    <2>6. CASE cntns(self)     BY <2>6 DEF cntns
    <2>7. CASE onSnc(self)     BY <2>7 DEF onSnc
    <2>8. CASE isMth(self)     BY <2>8 DEF isMth
    <2>9. CASE insrt(self)     BY <2>9 DEF insrt
    <2>10. CASE cas(self)      BY <2>10 DEF cas
    <2>11. CASE tryEv(self)    BY <2>11 DEF tryEv
    <2>12. CASE waitIns(self)
      \* Pushes frame with .ei = ei[self], then ei' = [ei EXCEPT ![self] = 1].
      <3>. USE <2>12 DEF waitIns
      <3>1. ei'[self] = 1
        OBVIOUS
      <3>2. \A s2 \in ProcSet : s2 # self => ei'[s2] = ei[s2]
        OBVIOUS
      <3>3. ei' \in [ProcSet -> Nat]
        BY <3>1, <3>2
      <3>4. ei[self] \in Nat
        OBVIOUS
      <3>5. stack'[self] =
              <<[procedure |-> "Evict", pc |-> "endEv",
                 ei |-> ei[self], ej |-> ej[self], lo |-> lo[self]]>>
              \o stack[self]
        OBVIOUS
      <3>6. Head(stack'[self]).ei = ei[self]
        BY <3>5
      <3>7. Head(stack'[self]).ei \in Nat
        BY <3>4, <3>6
      <3>8. \A s2 \in ProcSet : s2 # self => stack'[s2] = stack[s2]
        OBVIOUS
      <3>9. \A s2 \in ProcSet :
                stack'[s2] # <<>> => Head(stack'[s2]).ei \in Nat
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, stack'[s2] # <<>>
                      PROVE  Head(stack'[s2]).ei \in Nat
          OBVIOUS
        <4>1. CASE s2 = self
          BY <3>7, <4>1
        <4>2. CASE s2 # self
          <5>1. stack'[s2] = stack[s2]
            BY <3>8, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>3, <3>9
    <2>13. CASE endEv(self)    BY <2>13 DEF endEv
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
                  <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* `EjType': `ej[self] \in Int' (can go negative through nestedIns'        *)
(* decrement), together with a stack-frame constraint mirroring `EiType'.  *)
(*                                                                         *)
(* Used to discharge `mod(ej[self], K) \in 1..K' when reasoning about the  *)
(* THEN branch of `nestedIns' and about `set'.                             *)
(***************************************************************************)
EjType ==
  /\ ej \in [ProcSet -> Int]
  /\ \A self \in ProcSet :
        stack[self] # <<>> => Head(stack[self]).ej \in Int

LEMMA InitEjType == Init => EjType
  <1>. SUFFICES ASSUME Init  PROVE EjType
    OBVIOUS
  <1>1. ej = [self \in ProcSet |-> 1]
    BY DEF Init
  <1>2. ej \in [ProcSet -> Int]
    BY <1>1 DEF EjType
  <1>3. \A self \in ProcSet : stack[self] = <<>>
    BY DEF Init
  <1>. QED  BY <1>2, <1>3 DEF EjType

LEMMA EjTypeInd ==
  StackOK /\ EiType /\ EjType /\ [Next]_vars => EjType'
  <1>. SUFFICES ASSUME StackOK, EiType, EjType, [Next]_vars
                PROVE  EjType'
    OBVIOUS
  <1>. USE DEF EjType, EiType, StackOK, EvictLabels, WriterLabels, ProcSet
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  EjType'
    <2>. USE <1>2 DEF Evict
    <2>1. CASE strIns(self)
      BY <2>1 DEF strIns
    <2>2. CASE nestedIns(self)
      \* THEN: ej' = [ej EXCEPT ![self] = ej[self] - 1]; ELSE: UNCHANGED ej.
      <3>. USE <2>2 DEF nestedIns
      <3>1. stack' = stack  OBVIOUS
      <3>2. CASE compare(lo[self], mod(ei[self] + 1, K),
                          table[mod(ej[self], K)], mod(ej[self], K)) <= -1
        <4>1. ej'[self] = ej[self] - 1  BY <3>2
        <4>2. ej[self] \in Int  OBVIOUS
        <4>3. ej'[self] \in Int  BY <4>1, <4>2
        <4>4. \A s2 \in ProcSet : s2 # self => ej'[s2] = ej[s2]
          BY <3>2
        <4>. QED  BY <3>1, <4>3, <4>4
      <3>3. CASE ~(compare(lo[self], mod(ei[self] + 1, K),
                            table[mod(ej[self], K)], mod(ej[self], K)) <= -1)
        <4>1. UNCHANGED ej  BY <3>3
        <4>. QED  BY <3>1, <4>1
      <3>. QED  BY <3>2, <3>3
    <2>3. CASE set(self)
      \* ej' = [ej EXCEPT ![self] = ei[self] + 1]; stack UNCHANGED.
      <3>. USE <2>3 DEF set
      <3>1. stack' = stack  OBVIOUS
      <3>2. ej'[self] = ei[self] + 1
        OBVIOUS
      <3>3. ei[self] \in Nat
        OBVIOUS
      <3>4. ej'[self] \in Int
        BY <3>2, <3>3
      <3>5. \A s2 \in ProcSet : s2 # self => ej'[s2] = ej[s2]
        OBVIOUS
      <3>6. ej' \in [ProcSet -> Int]
        BY <3>4, <3>5
      <3>. QED  BY <3>1, <3>6
    <2>4. CASE flush(self)
      BY <2>4 DEF flush
    <2>5. CASE rtrn(self)
      \* Pops stack; ej'[self] = Head(stack[self]).ej.
      <3>. USE <2>5 DEF rtrn
      <3>1. pc[self] = "rtrn"  OBVIOUS
      <3>2. pc[self] \in EvictLabels  BY <3>1
      <3>3. stack[self] # <<>>  BY <3>2
      <3>4. Head(stack[self]).ej \in Int  BY <3>3
      <3>5. ej'[self] = Head(stack[self]).ej  OBVIOUS
      <3>6. ej'[self] \in Int  BY <3>4, <3>5
      <3>7. \A s2 \in ProcSet : s2 # self => ej'[s2] = ej[s2]
        OBVIOUS
      <3>8. ej' \in [ProcSet -> Int]
        BY <3>6, <3>7
      \* Post-state stack: empty at self, unchanged at others.
      <3>9. stack'[self] = Tail(stack[self])
        OBVIOUS
      <3>10. Tail(stack[self]) = <<>>
        BY <3>2
      <3>11. stack'[self] = <<>>
        BY <3>9, <3>10
      <3>12. \A s2 \in ProcSet :
                stack'[s2] # <<>> => Head(stack'[s2]).ej \in Int
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, stack'[s2] # <<>>
                      PROVE  Head(stack'[s2]).ej \in Int
          OBVIOUS
        <4>1. CASE s2 = self
          BY <3>11, <4>1
        <4>2. CASE s2 # self
          <5>1. stack'[s2] = stack[s2]
            BY <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>8, <3>12
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  EjType'
    <2>. USE <1>3, ProcSetIsWriter DEF p
    <2>1. CASE pick(self)      BY <2>1 DEF pick
    <2>2. CASE put(self)       BY <2>2 DEF put
    <2>3. CASE waitEv(self)    BY <2>3 DEF waitEv
    <2>4. CASE endWEv(self)    BY <2>4 DEF endWEv
    <2>5. CASE chkSnc(self)    BY <2>5 DEF chkSnc
    <2>6. CASE cntns(self)     BY <2>6 DEF cntns
    <2>7. CASE onSnc(self)     BY <2>7 DEF onSnc
    <2>8. CASE isMth(self)     BY <2>8 DEF isMth
    <2>9. CASE insrt(self)     BY <2>9 DEF insrt
    <2>10. CASE cas(self)      BY <2>10 DEF cas
    <2>11. CASE tryEv(self)    BY <2>11 DEF tryEv
    <2>12. CASE waitIns(self)
      \* Pushes frame with .ej = ej[self], then ej' = [ej EXCEPT ![self] = 1].
      <3>. USE <2>12 DEF waitIns
      <3>1. ej'[self] = 1
        OBVIOUS
      <3>2. \A s2 \in ProcSet : s2 # self => ej'[s2] = ej[s2]
        OBVIOUS
      <3>3. ej' \in [ProcSet -> Int]
        BY <3>1, <3>2
      <3>4. ej[self] \in Int
        OBVIOUS
      <3>5. stack'[self] =
              <<[procedure |-> "Evict", pc |-> "endEv",
                 ei |-> ei[self], ej |-> ej[self], lo |-> lo[self]]>>
              \o stack[self]
        OBVIOUS
      <3>6. Head(stack'[self]).ej = ej[self]
        BY <3>5
      <3>7. Head(stack'[self]).ej \in Int
        BY <3>4, <3>6
      <3>8. \A s2 \in ProcSet : s2 # self => stack'[s2] = stack[s2]
        OBVIOUS
      <3>9. \A s2 \in ProcSet :
                stack'[s2] # <<>> => Head(stack'[s2]).ej \in Int
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, stack'[s2] # <<>>
                      PROVE  Head(stack'[s2]).ej \in Int
          OBVIOUS
        <4>1. CASE s2 = self
          BY <3>7, <4>1
        <4>2. CASE s2 # self
          <5>1. stack'[s2] = stack[s2]
            BY <3>8, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>3, <3>9
    <2>13. CASE endEv(self)    BY <2>13 DEF endEv
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
                  <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* `EvictExclusive': at most one writer at a time is inside the "evictor   *)
(* territory" `EvictLabels \cup {"endEv"}', and whenever any writer is     *)
(* there, `evict = TRUE'.                                                  *)
(*                                                                         *)
(* This is the standard mutual-exclusion invariant of the Evict            *)
(* procedure.  It is used to discharge the third conjunct of `DupInv'      *)
(* for the `nestedIns' THEN, `set', and `flush outer-else' actions (where  *)
(* the question "is some other writer at `rtrn' or `endEv'?" arises).      *)
(*                                                                         *)
(* The invariant is inductive at every action except `waitIns', whose      *)
(* precondition `waitCnt = Cardinality(Writer) - 1 + Cardinality(Reader)'  *)
(* is supposed to pin down the count of other writers blocked at           *)
(* `{"waitEv", "endWEv"}'.  Discharging the `waitIns' case would require   *)
(* a standalone `WaitCntInv' linking `waitCnt' to that count; we leave     *)
(* that one case OMITTED here as a single localised stub.                  *)
(***************************************************************************)
EvictUnion == EvictLabels \cup {"endEv"}

EvictExclusive ==
  /\ \A s1, s2 \in Writer :
       (pc[s1] \in EvictUnion /\ pc[s2] \in EvictUnion) => s1 = s2
  /\ \A s \in Writer :
       pc[s] \in EvictUnion => evict = TRUE

LEMMA InitEvictExclusive == Init => EvictExclusive
  <1>. SUFFICES ASSUME Init  PROVE EvictExclusive
    OBVIOUS
  <1>1. \A s \in Writer : pc[s] = "pick"
    BY ProcSetIsWriter DEF Init, ProcSet
  <1>2. \A s \in Writer : pc[s] \notin EvictUnion
    BY <1>1 DEF EvictUnion, EvictLabels
  <1>. QED  BY <1>2 DEF EvictExclusive

LEMMA EvictExclusiveInd ==
  Inv /\ StackOK /\ EvictExclusive /\ [Next]_vars => EvictExclusive'
  <1>. SUFFICES ASSUME Inv, StackOK, EvictExclusive, [Next]_vars
                PROVE  EvictExclusive'
    OBVIOUS
  <1>. USE DEF EvictExclusive, EvictUnion, EvictLabels, WriterLabels,
              ProcSet, StackOK, Inv, PcRangeOK, PcRange
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  EvictExclusive'
    \* Every Evict-procedure action keeps pc[self] in EvictLabels (rtrn
    \* transitions into "endEv" which is still in EvictUnion).  No other
    \* process's pc changes, and `evict' is unchanged across all Evict
    \* actions.  Hence the mutex and the `evict = TRUE' conjunct are
    \* preserved.
    <2>. USE <1>2, ProcSetIsWriter DEF Evict
    <2>1. CASE strIns(self)
      <3>. USE <2>1 DEF strIns
      <3>1. pc[self] \in EvictLabels  OBVIOUS
      <3>2. pc'[self] \in EvictLabels  OBVIOUS
      <3>3. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>4. evict' = evict  OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4
    <2>2. CASE nestedIns(self)
      <3>. USE <2>2 DEF nestedIns
      <3>1. pc[self] \in EvictLabels  OBVIOUS
      <3>2. pc'[self] \in EvictLabels  OBVIOUS
      <3>3. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>4. evict' = evict  OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4
    <2>3. CASE set(self)
      <3>. USE <2>3 DEF set
      <3>1. pc[self] \in EvictLabels  OBVIOUS
      <3>2. pc'[self] \in EvictLabels  OBVIOUS
      <3>3. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>4. evict' = evict  OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4
    <2>4. CASE flush(self)
      <3>. USE <2>4 DEF flush
      <3>1. pc[self] \in EvictLabels  OBVIOUS
      <3>2. pc'[self] \in EvictLabels  OBVIOUS
      <3>3. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>4. evict' = evict  OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4
    <2>5. CASE rtrn(self)
      \* "rtrn" -> "endEv", still in EvictUnion.
      <3>. USE <2>5 DEF rtrn
      <3>1. pc[self] = "rtrn"  OBVIOUS
      <3>2. pc[self] \in EvictUnion  BY <3>1
      <3>3. stack[self] # <<>>  BY <3>1
      <3>4. Head(stack[self]).pc = "endEv"  BY <3>3
      <3>5. pc'[self] = "endEv"  BY <3>4
      <3>6. pc'[self] \in EvictUnion  BY <3>5
      <3>7. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>8. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>6, <3>7, <3>8
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  EvictExclusive'
    <2>. USE <1>3, ProcSetIsWriter DEF p
    <2>1. CASE pick(self)
      <3>. USE <2>1 DEF pick
      <3>1. pc[self] = "pick"  OBVIOUS
      <3>2. pc[self] \notin EvictUnion  BY <3>1
      <3>3. pc'[self] \in {"put", "Done"}  OBVIOUS
      <3>4. pc'[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>2. CASE put(self)
      <3>. USE <2>2 DEF put
      <3>1. pc[self] = "put"  OBVIOUS
      <3>2. pc[self] \notin EvictUnion  BY <3>1
      <3>3. pc'[self] \in {"waitEv", "chkSnc"}  OBVIOUS
      <3>4. pc'[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>3. CASE waitEv(self)
      <3>. USE <2>3 DEF waitEv
      <3>1. pc'[self] = "endWEv"  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "waitEv"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>4. CASE endWEv(self)
      <3>. USE <2>4 DEF endWEv
      <3>1. pc'[self] = "put"  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "endWEv"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>5. CASE chkSnc(self)
      <3>. USE <2>5 DEF chkSnc
      <3>1. pc'[self] \in {"cntns", "insrt"}  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "chkSnc"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>6. CASE cntns(self)
      <3>. USE <2>6 DEF cntns
      <3>1. pc'[self] \in {"pick", "onSnc", "cntns"}  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "cntns"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>7. CASE onSnc(self)
      <3>. USE <2>7 DEF onSnc
      <3>1. pc'[self] \in {"pick", "insrt"}  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "onSnc"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>8. CASE insrt(self)
      <3>. USE <2>8 DEF insrt
      <3>1. pc'[self] \in {"cas", "isMth", "tryEv"}  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "insrt"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>9. CASE isMth(self)
      <3>. USE <2>9 DEF isMth
      <3>1. pc'[self] \in {"pick", "insrt"}  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "isMth"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>10. CASE cas(self)
      <3>. USE <2>10 DEF cas
      <3>1. pc'[self] \in {"pick", "insrt"}  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "cas"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>. QED  BY <3>2, <3>4, <3>5, <3>6
    <2>11. CASE tryEv(self)
      \* tryEv may flip `evict' from FALSE to TRUE, but `pc'[self]' goes
      \* to "waitIns" or "put", neither of which is in EvictUnion.  The
      \* `evict = TRUE' conjunct is strengthened (never weakened).
      <3>. USE <2>11 DEF tryEv
      <3>1. pc'[self] \in {"waitIns", "put"}  OBVIOUS
      <3>2. pc'[self] \notin EvictUnion  BY <3>1
      <3>3. pc[self] = "tryEv"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      \* evict' \in {TRUE, evict}: either strengthened or unchanged.
      <3>6. evict' = TRUE \/ evict' = evict  OBVIOUS
      <3>. QED
        <4>1. \A s1, s2 \in Writer :
                (pc'[s1] \in EvictUnion /\ pc'[s2] \in EvictUnion)
                => s1 = s2
          <5>. SUFFICES ASSUME NEW s1 \in Writer, NEW s2 \in Writer,
                                pc'[s1] \in EvictUnion,
                                pc'[s2] \in EvictUnion
                        PROVE  s1 = s2
            OBVIOUS
          <5>1. s1 # self  BY <3>2
          <5>2. s2 # self  BY <3>2
          <5>3. pc'[s1] = pc[s1]  BY <3>5, <5>1
          <5>4. pc'[s2] = pc[s2]  BY <3>5, <5>2
          <5>5. pc[s1] \in EvictUnion  BY <5>3
          <5>6. pc[s2] \in EvictUnion  BY <5>4
          <5>. QED  BY <5>5, <5>6
        <4>2. \A s \in Writer : pc'[s] \in EvictUnion => evict' = TRUE
          <5>. SUFFICES ASSUME NEW s \in Writer, pc'[s] \in EvictUnion
                        PROVE  evict' = TRUE
            OBVIOUS
          <5>1. s # self  BY <3>2
          <5>2. pc'[s] = pc[s]  BY <3>5, <5>1
          <5>3. pc[s] \in EvictUnion  BY <5>2
          <5>4. evict = TRUE  BY <5>3
          <5>. QED  BY <5>4, <3>6
        <4>. QED  BY <4>1, <4>2
    <2>12. CASE waitIns(self)
      \* waitIns transitions pc[self] from "waitIns" to "strIns" (enters
      \* EvictUnion).  Preservation requires that no OTHER process is
      \* in EvictUnion pre-state.  This follows from the waitCnt
      \* precondition `waitCnt = Cardinality(Writer) - 1 + Cardinality(Reader)',
      \* combined with a WaitCntInv linking `waitCnt' to
      \* `|{s \in Writer : pc[s] \in {"waitEv", "endWEv"}}|'.  We do not
      \* formalise WaitCntInv here and leave this one case OMITTED.
      OMITTED
    <2>13. CASE endEv(self)
      \* endEv transitions pc[self] from "endEv" (in EvictUnion) to "put"
      \* (not in EvictUnion); evict' = FALSE.  By EvictExclusive pre,
      \* self is the UNIQUE writer in EvictUnion.  After the transition,
      \* NO writer is in EvictUnion.  Both conjuncts become vacuously true.
      <3>. USE <2>13 DEF endEv
      <3>1. pc[self] = "endEv"  OBVIOUS
      <3>2. pc[self] \in EvictUnion  BY <3>1
      <3>3. pc'[self] = "put"  OBVIOUS
      <3>4. pc'[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. \A s2 \in Writer : s2 # self => pc[s2] \notin EvictUnion
        <4>. SUFFICES ASSUME NEW s2 \in Writer, s2 # self,
                              pc[s2] \in EvictUnion
                      PROVE  FALSE
          OBVIOUS
        <4>1. s2 = self
          BY <3>2
        <4>. QED  BY <4>1
      <3>7. \A s2 \in Writer : pc'[s2] \notin EvictUnion
        <4>. SUFFICES ASSUME NEW s2 \in Writer
                      PROVE  pc'[s2] \notin EvictUnion
          OBVIOUS
        <4>1. CASE s2 = self
          BY <3>4, <4>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <3>5, <4>2
          <5>2. pc[s2] \notin EvictUnion  BY <3>6, <4>2
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>7
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
                  <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* `LoType': conditional typing of `lo' at the places where the Evict      *)
(* procedure is about to write it into the `table'.  Specifically, at      *)
(* every writer whose `pc' is in `{"nestedIns", "set"}', `lo[self]' is     *)
(* a `TableValues' element.                                                *)
(*                                                                         *)
(* Used to discharge the `set' case of `DupInvNext' (the value written     *)
(* into `table[mod(ej+1, K)]' is `lo[self]', which must be in              *)
(* `TableValues' for `TableType'' to hold).                                *)
(***************************************************************************)
LoType ==
  \A self \in ProcSet :
    pc[self] \in {"nestedIns", "set"} => lo[self] \in TableValues

LEMMA InitLoType == Init => LoType
  <1>. SUFFICES ASSUME Init  PROVE LoType
    OBVIOUS
  <1>1. \A self \in ProcSet : pc[self] = "pick"
    BY ProcSetIsWriter DEF Init, ProcSet
  <1>2. \A self \in ProcSet : pc[self] \notin {"nestedIns", "set"}
    BY <1>1
  <1>. QED  BY <1>2 DEF LoType

LEMMA LoTypeInd ==
  Inv /\ StackOK /\ EiType /\ DupInv /\ LoType /\ [Next]_vars => LoType'
  <1>. SUFFICES ASSUME Inv, StackOK, EiType, DupInv, LoType, [Next]_vars
                PROVE  LoType'
    OBVIOUS
  <1>. USE DEF LoType, EiType, DupInv, TableType, TableValues,
              StackOK, EvictLabels, WriterLabels, ProcSet,
              Inv, PcRangeOK, PcRange
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  LoType'
    <2>. USE <1>2 DEF Evict
    <2>. SUFFICES ASSUME NEW s2 \in ProcSet,
                          pc'[s2] \in {"nestedIns", "set"}
                  PROVE  lo'[s2] \in TableValues
      BY DEF LoType
    <2>1. CASE strIns(self)
      \* strIns: ei[self] <= K+L -> pc'[self] = "nestedIns",
      \*   lo'[self] = table[mod(ei[self] + 1, K)] \in TableValues.
      \* Otherwise -> pc'[self] = "flush", lo UNCHANGED.
      <3>. USE <2>1 DEF strIns
      <3>1. CASE s2 = self
        <4>1. CASE ei[self] <= K+L
          <5>1. lo'[self] = table[mod(ei[self] + 1, K)]
            BY <4>1
          \* pin mod(ei[self] + 1, K) \in 1..K
          <5>2. ei[self] \in Nat  OBVIOUS
          <5>3. ei[self] + 1 \in Nat  BY <5>2
          <5>4. K \in Nat \ {0}  BY OAAssumption
          <5>5. (ei[self] + 1) % K \in 0..(K-1)
            BY <5>3, <5>4
          <5>6. mod(ei[self] + 1, K) \in 1..K
            BY <5>4, <5>5 DEF mod
          <5>7. table[mod(ei[self] + 1, K)] \in TableValues
            BY <5>6
          <5>. QED  BY <3>1, <5>1, <5>7
        <4>2. CASE ~(ei[self] <= K+L)
          \* pc'[self] = "flush", s2 = self means pc'[s2] = "flush",
          \* which is not in {"nestedIns", "set"}.  Contradiction.
          <5>1. pc'[self] = "flush"  BY <4>2
          <5>2. pc'[self] \notin {"nestedIns", "set"}
            BY <5>1
          <5>. QED  BY <3>1, <5>2
        <4>. QED  BY <4>1, <4>2
      <3>2. CASE s2 # self
        <4>1. pc'[s2] = pc[s2]  BY <3>2
        <4>2. pc[s2] \in {"nestedIns", "set"}  BY <4>1
        <4>3. lo'[s2] = lo[s2]
          \* Both branches of strIns only write lo at self, not s2.
          BY <3>2
        <4>4. lo[s2] \in TableValues
          BY <4>2
        <4>. QED  BY <4>3, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>2. CASE nestedIns(self)
      \* nestedIns leaves lo UNCHANGED.  Any s2 with pc'[s2] \in
      \* {"nestedIns", "set"} either has pc[s2] \in {"nestedIns",
      \* "set"} pre-state (so lo[s2] \in TableValues by LoType) and
      \* lo'[s2] = lo[s2]; or was at pc[s2] = "nestedIns" and stayed
      \* in the set.
      <3>. USE <2>2 DEF nestedIns
      <3>1. lo' = lo  OBVIOUS
      <3>2. CASE s2 = self
        \* pc'[self] \in {"nestedIns", "set"}; pc[self] = "nestedIns"
        \* \in {"nestedIns", "set"}; LoType gives lo[self] \in TableValues.
        <4>1. pc[self] = "nestedIns"  OBVIOUS
        <4>2. lo[self] \in TableValues  BY <4>1
        <4>3. lo'[self] = lo[self]  BY <3>1
        <4>. QED  BY <3>2, <4>2, <4>3
      <3>3. CASE s2 # self
        <4>1. pc'[s2] = pc[s2]  BY <3>3
        <4>2. pc[s2] \in {"nestedIns", "set"}  BY <4>1
        <4>3. lo'[s2] = lo[s2]  BY <3>1
        <4>. QED  BY <4>2, <4>3
      <3>. QED  BY <3>2, <3>3
    <2>3. CASE set(self)
      \* set: pc'[self] = "strIns" \notin {"nestedIns", "set"}.
      \* For s2 # self, pc'[s2] = pc[s2] and lo'[s2] = lo[s2] (lo
      \* UNCHANGED by set).
      <3>. USE <2>3 DEF set
      <3>1. pc'[self] = "strIns"  OBVIOUS
      <3>2. lo' = lo  OBVIOUS
      <3>3. CASE s2 = self
        <4>1. pc'[self] \notin {"nestedIns", "set"}  BY <3>1
        <4>. QED  BY <3>3, <4>1
      <3>4. CASE s2 # self
        <4>1. pc'[s2] = pc[s2]  BY <3>4
        <4>2. pc[s2] \in {"nestedIns", "set"}  BY <4>1
        <4>3. lo'[s2] = lo[s2]  BY <3>2
        <4>. QED  BY <4>2, <4>3
      <3>. QED  BY <3>3, <3>4
    <2>4. CASE flush(self)
      \* flush: pc'[self] \in {"flush", "rtrn"}, neither in
      \* {"nestedIns", "set"}.  For s2 # self, pc and lo unchanged
      \* at s2.
      <3>. USE <2>4 DEF flush
      <3>1. pc'[self] \in {"flush", "rtrn"}  OBVIOUS
      <3>2. pc'[self] \notin {"nestedIns", "set"}  BY <3>1
      <3>3. CASE s2 = self
        <4>. QED  BY <3>3, <3>2
      <3>4. CASE s2 # self
        <4>1. pc'[s2] = pc[s2]  BY <3>4
        <4>2. pc[s2] \in {"nestedIns", "set"}  BY <4>1
        <4>3. lo'[s2] = lo[s2]  BY <3>4
        <4>4. lo[s2] \in TableValues  BY <4>2
        <4>. QED  BY <4>3, <4>4
      <3>. QED  BY <3>3, <3>4
    <2>5. CASE rtrn(self)
      \* rtrn: pc'[self] = "endEv" (by StackOK), not in {"nestedIns",
      \* "set"}.  For s2 # self, unchanged.
      <3>. USE <2>5 DEF rtrn
      <3>1. pc[self] = "rtrn"  OBVIOUS
      <3>2. stack[self] # <<>>  BY <3>1
      <3>3. Head(stack[self]).pc = "endEv"  BY <3>2
      <3>4. pc'[self] = "endEv"  BY <3>3
      <3>5. pc'[self] \notin {"nestedIns", "set"}  BY <3>4
      <3>6. CASE s2 = self
        <4>. QED  BY <3>6, <3>5
      <3>7. CASE s2 # self
        <4>1. pc'[s2] = pc[s2]  BY <3>7
        <4>2. pc[s2] \in {"nestedIns", "set"}  BY <4>1
        <4>3. lo'[s2] = lo[s2]  BY <3>7
        <4>4. lo[s2] \in TableValues  BY <4>2
        <4>. QED  BY <4>3, <4>4
      <3>. QED  BY <3>6, <3>7
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  LoType'
    \* p-actions live in WriterLabels, never enter {"nestedIns", "set"},
    \* and (with one exception) leave `lo' UNCHANGED.  waitIns writes
    \* lo'[self] = 0 but pc'[self] = "strIns", still not in
    \* {"nestedIns", "set"}.  For any s2 with pc'[s2] \in {"nestedIns",
    \* "set"}, s2 # self (since pc'[self] \notin that set) so
    \* lo'[s2] = lo[s2] and we close by LoType pre-state.
    <2>. USE <1>3, ProcSetIsWriter DEF p
    <2>. SUFFICES ASSUME NEW s2 \in ProcSet,
                          pc'[s2] \in {"nestedIns", "set"}
                  PROVE  lo'[s2] \in TableValues
      BY DEF LoType
    <2>1. CASE pick(self)      BY <2>1 DEF pick
    <2>2. CASE put(self)       BY <2>2 DEF put
    <2>3. CASE waitEv(self)    BY <2>3 DEF waitEv
    <2>4. CASE endWEv(self)    BY <2>4 DEF endWEv
    <2>5. CASE chkSnc(self)    BY <2>5 DEF chkSnc
    <2>6. CASE cntns(self)     BY <2>6 DEF cntns
    <2>7. CASE onSnc(self)     BY <2>7 DEF onSnc
    <2>8. CASE isMth(self)     BY <2>8 DEF isMth
    <2>9. CASE insrt(self)     BY <2>9 DEF insrt
    <2>10. CASE cas(self)      BY <2>10 DEF cas
    <2>11. CASE tryEv(self)    BY <2>11 DEF tryEv
    <2>12. CASE waitIns(self)
      \* waitIns writes lo'[self] = 0 and pc'[self] = "strIns".
      <3>. USE <2>12 DEF waitIns
      <3>1. pc'[self] = "strIns"  OBVIOUS
      <3>2. pc'[self] \notin {"nestedIns", "set"}  BY <3>1
      <3>3. s2 # self  BY <3>2
      <3>4. pc'[s2] = pc[s2]  BY <3>3
      <3>5. lo'[s2] = lo[s2]  BY <3>3
      <3>6. pc[s2] \in {"nestedIns", "set"}  BY <3>4
      <3>. QED  BY <3>5, <3>6
    <2>13. CASE endEv(self)    BY <2>13 DEF endEv
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
                  <2>8, <2>9, <2>10, <2>11, <2>12, <2>13
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* Inductive step.                                                         *)
(*                                                                         *)
(* Most writer disjuncts leave `table' and `evict' UNCHANGED and move      *)
(* `pc[self]' to a label NOT in `{"rtrn", "endEv"}'.  Each of those is     *)
(* discharged by routine case-by-case unfolding.  The two interesting      *)
(* writer disjuncts are:                                                   *)
(*                                                                         *)
(*   - `cas': may modify `table' (success branch).  The failed-CAS branch  *)
(*     is discharged with the help of `ResultType'; the success branch    *)
(*     is OMITTED -- see (a) in the doc-comment above.                     *)
(*   - `endEv': flips `evict' from TRUE to FALSE.  Discharged via the      *)
(*     post-flush pc invariant (third conjunct of DupInv).                 *)
(*                                                                         *)
(* For the Evict procedure body, `strIns' and `rtrn' leave `table'         *)
(* UNCHANGED and are fully discharged.  `flush' inner-then is discharged   *)
(* with the help of `EiType' (needed to pin `mod(ei[self], K) \in 1..K').  *)
(*                                                                         *)
(* `nestedIns' (THEN branch) is now FULLY DISCHARGED using the mutex       *)
(* invariant `EvictExclusive' (no other writer is at {"rtrn","endEv"}      *)
(* while self is in the Evict procedure, and evict = TRUE in those         *)
(* states makes FindOrPut' vacuous) together with `EjType' (pinning        *)
(* the overwritten and source cells to 1..K).                              *)
(*                                                                         *)
(* `set' is MOSTLY DISCHARGED: FindOrPut' => NoDupsTable' and the third    *)
(* conjunct close via the same `EvictExclusive' + `EjType' route; the      *)
(* residual OMITTED is the single fact `lo[self] \in TableValues' at       *)
(* pc = "set" -- it would follow from a conditional `LoType' invariant     *)
(* tracking `lo' through `strIns'.                                         *)
(*                                                                         *)
(* `flush' outer-else is MOSTLY DISCHARGED: TableType' (UNCHANGED table)   *)
(* and FindOrPut' => NoDupsTable' (EvictExclusive forces evict = TRUE)     *)
(* close; the residual OMITTED is the single fact `NoDupsTable' at pc     *)
(* = "flush", which requires the sort-permutation / insertion-sort-body    *)
(* invariant -- see (b)/(c).                                               *)
(***************************************************************************)
LEMMA DupInvNext == Inv /\ ResultType /\ EiType /\ EjType /\ LoType
                    /\ EvictExclusive /\ DupInv
                    /\ [Next]_vars => DupInv'
  <1>. SUFFICES ASSUME Inv, ResultType, EiType, EjType, LoType,
                       EvictExclusive, DupInv, [Next]_vars
                PROVE  DupInv'
    OBVIOUS
  <1>. USE DEF DupInv, TableType, NoDupsTable, FindOrPut, TableValues,
              Inv, PcRangeOK, ProcSet, ResultType, EiType
  (***********************************************************************)
  (* Stutter.                                                              *)
  (***********************************************************************)
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  (***********************************************************************)
  (* Evict procedure disjuncts.                                            *)
  (***********************************************************************)
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  DupInv'
    <2>1. CASE strIns(self)
      \* table is in UNCHANGED.  pc'[self] in {"nestedIns", "flush"}.
      <3>. USE <2>1 DEF strIns
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'
        BY <3>1
      <3>3. FindOrPut' => NoDupsTable'
        BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"nestedIns", "flush"}
            OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]
            BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>2. CASE nestedIns(self)
      \* Split the two branches of the `nestedIns' IF:
      \*   (A) THEN (compare <= -1): table is modified (a cell is copied
      \*       from `mod(ej,K)' into `mod(ej+1,K)').  TableType' follows
      \*       directly from TableType (the written value is a pre-state
      \*       table cell, already in TableValues).  FindOrPut' =>
      \*       NoDupsTable' is vacuous: `pc[self] = "nestedIns" \in
      \*       EvictLabels' forces `evict = TRUE' via `EvictExclusive',
      \*       which UNCHANGED carries to `evict' = TRUE', so
      \*       `FindOrPut' = FALSE'.  The third conjunct is vacuous: at
      \*       any s2 # self with `pc'[s2] \in {"rtrn","endEv"}' the pre
      \*       state already has `pc[s2] \in EvictUnion', contradicting
      \*       `EvictExclusive' at self \in EvictUnion.
      \*   (B) ELSE: UNCHANGED <<table, evict>> (only pc and ej update);
      \*       this branch is fully discharged here along the same lines as
      \*       `strIns', `tryEv', etc.
      <3>. USE <2>2 DEF nestedIns
      <3>A. CASE compare(lo[self], mod(ei[self] + 1, K),
                          table[mod(ej[self], K)], mod(ej[self], K)) <= -1
        <4>. USE <3>A, ProcSetIsWriter
             DEF EjType, EvictExclusive, EvictUnion, EvictLabels
        <4>. DEFINE pos1 == mod(ej[self] + 1, K)
        <4>. DEFINE pos2 == mod(ej[self], K)
        <4>1. table' = [table EXCEPT ![pos1] = table[pos2]]
          OBVIOUS
        <4>2. evict' = evict  OBVIOUS
        <4>3. pc[self] = "nestedIns"  OBVIOUS
        <4>4. pc[self] \in EvictUnion  BY <4>3
        \* pin pos1, pos2 \in 1..K
        <4>5. ej[self] \in Int  OBVIOUS
        <4>6. ej[self] + 1 \in Int  BY <4>5
        <4>7. K \in Nat \ {0}  BY OAAssumption
        <4>8. ej[self] % K \in 0..(K-1)  BY <4>5, <4>7
        <4>9. (ej[self] + 1) % K \in 0..(K-1)  BY <4>6, <4>7
        <4>10. pos2 \in 1..K  BY <4>7, <4>8 DEF mod
        <4>11. pos1 \in 1..K  BY <4>7, <4>9 DEF mod
        \* evict = TRUE via EvictExclusive at self.
        <4>12. evict = TRUE  BY <4>4
        <4>13. evict' = TRUE  BY <4>2, <4>12
        \* TableType': each cell remains in TableValues after the copy.
        <4>14. TableType'
          <5>. SUFFICES ASSUME NEW j \in 1..K
                        PROVE  table'[j] \in TableValues
            BY <4>1
          <5>1. table[pos2] \in TableValues
            BY <4>10
          <5>2. CASE j = pos1
            <6>1. table'[j] = table[pos2]
              BY <4>1, <4>11, <5>2
            <6>. QED  BY <6>1, <5>1
          <5>3. CASE j # pos1
            <6>1. table'[j] = table[j]
              BY <4>1, <4>11, <5>3
            <6>. QED  BY <6>1
          <5>. QED  BY <5>2, <5>3
        \* FindOrPut' => NoDupsTable': vacuous because evict' = TRUE.
        <4>15. FindOrPut' => NoDupsTable'
          <5>. SUFFICES ASSUME FindOrPut'  PROVE NoDupsTable'
            OBVIOUS
          <5>1. evict' = FALSE  BY DEF FindOrPut
          <5>. QED  BY <4>13, <5>1
        \* Third conjunct: no OTHER process is in EvictUnion pre-state
        \* (mutex); self's post-pc stays out of {"rtrn", "endEv"}.
        <4>16. \A s2 \in ProcSet :
                  pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"rtrn", "endEv"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 \in Writer  BY ProcSetIsWriter
          <5>2. CASE s2 = self
            <6>1. pc'[self] \in {"set", "nestedIns"}  OBVIOUS
            <6>2. pc'[self] \notin {"rtrn", "endEv"}  BY <6>1
            <6>. QED  BY <5>2, <6>2
          <5>3. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <5>3
            <6>2. pc[s2] \in {"rtrn", "endEv"}  BY <6>1
            <6>3. pc[s2] \in EvictUnion  BY <6>2
            <6>4. s2 = self  BY <4>4, <5>1, <6>3
            <6>. QED  BY <5>3, <6>4
          <5>. QED  BY <5>2, <5>3
        <4>. QED  BY <4>14, <4>15, <4>16
      <3>B. CASE ~(compare(lo[self], mod(ei[self] + 1, K),
                            table[mod(ej[self], K)], mod(ej[self], K)) <= -1)
        \* ELSE: UNCHANGED <<table, evict>>, pc'[self] = "set".
        <4>1. UNCHANGED <<table, evict>>
          BY <3>B
        <4>2. pc'[self] = "set"
          BY <3>B
        <4>3. TableType'
          BY <4>1
        <4>4. FindOrPut' => NoDupsTable'
          BY <4>1
        <4>5. \A s2 \in ProcSet :
                pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"rtrn", "endEv"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. CASE s2 = self
            <6>1. pc'[s2] = "set"
              BY <4>2, <5>1
            <6>. QED  BY <6>1
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]
              BY <5>2
            <6>. QED  BY <6>1, <4>1
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>3, <4>4, <4>5
      <3>. QED  BY <3>A, <3>B
    <2>3. CASE set(self)
      \* set: table' = [table EXCEPT ![mod(ej+1, K)] = lo[self]].
      \*
      \* Two of DupInv's three conjuncts close fully here using the same
      \* mutex argument as in `nestedIns' THEN:
      \*
      \*   - FindOrPut' => NoDupsTable': `pc[self] = "set" \in EvictLabels'
      \*     forces `evict = TRUE' by `EvictExclusive', hence `evict' =
      \*     TRUE' and FindOrPut' = FALSE (vacuous).
      \*
      \*   - \A s2 : pc'[s2] \in {"rtrn","endEv"} => NoDupsTable': at
      \*     self, pc'[self] = "strIns" \notin {"rtrn","endEv"}; at any
      \*     s2 # self, pc'[s2] = pc[s2] and pc[s2] \in EvictUnion
      \*     contradicts `EvictExclusive' (self \in EvictUnion).
      \*
      \* TableType' reduces to `lo[self] \in TableValues' (the value
      \* being written into table[mod(ej+1,K)]).  Establishing this
      \* requires a conditional `LoType' invariant tracking `lo[self]'
      \* through the strIns flow (set precondition pc[self] = "set"
      \* is reachable only after strIns writes `lo[self] := table[...]').
      \* We leave `lo[self] \in TableValues' as a single, localised
      \* OMITTED sub-step here; all the other set-case reasoning is
      \* discharged.
      <3>. USE <2>3, ProcSetIsWriter
           DEF set, EjType, LoType, EvictExclusive, EvictUnion, EvictLabels
      <3>. DEFINE pos == mod(ej[self] + 1, K)
      <3>1. table' = [table EXCEPT ![pos] = lo[self]]
        OBVIOUS
      <3>2. evict' = evict  OBVIOUS
      <3>3. pc[self] = "set"  OBVIOUS
      <3>4. pc[self] \in EvictUnion  BY <3>3
      <3>5. pc'[self] = "strIns"  OBVIOUS
      \* pin pos \in 1..K via EjType + OAAssumption.
      <3>6. ej[self] \in Int  OBVIOUS
      <3>7. ej[self] + 1 \in Int  BY <3>6
      <3>8. K \in Nat \ {0}  BY OAAssumption
      <3>9. (ej[self] + 1) % K \in 0..(K-1)  BY <3>7, <3>8
      <3>10. pos \in 1..K  BY <3>8, <3>9 DEF mod
      \* evict = TRUE via EvictExclusive at self.
      <3>11. evict = TRUE  BY <3>4
      <3>12. evict' = TRUE  BY <3>2, <3>11
      \* TableType': the value being written is `lo[self]'; at pc[self]
      \* = "set", `LoType' gives `lo[self] \in TableValues'.
      <3>13. lo[self] \in TableValues
        BY <3>3
      <3>14. TableType'
        <4>. SUFFICES ASSUME NEW j \in 1..K
                      PROVE  table'[j] \in TableValues
          BY <3>1
        <4>1. CASE j = pos
          <5>1. table'[j] = lo[self]
            BY <3>1, <3>10, <4>1
          <5>. QED  BY <5>1, <3>13
        <4>2. CASE j # pos
          <5>1. table'[j] = table[j]
            BY <3>1, <3>10, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      \* FindOrPut' => NoDupsTable': vacuous because evict' = TRUE.
      <3>15. FindOrPut' => NoDupsTable'
        <4>. SUFFICES ASSUME FindOrPut'  PROVE NoDupsTable'
          OBVIOUS
        <4>1. evict' = FALSE  BY DEF FindOrPut
        <4>. QED  BY <3>12, <4>1
      \* Third conjunct: no OTHER process is in EvictUnion pre-state;
      \* self's post-pc is "strIns", not in {"rtrn", "endEv"}.
      <3>16. \A s2 \in ProcSet :
                pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. s2 \in Writer  BY ProcSetIsWriter
        <4>2. CASE s2 = self
          <5>1. pc'[self] = "strIns"  BY <3>5
          <5>2. pc'[self] \notin {"rtrn", "endEv"}  BY <5>1
          <5>. QED  BY <4>2, <5>2
        <4>3. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>3
          <5>2. pc[s2] \in {"rtrn", "endEv"}  BY <5>1
          <5>3. pc[s2] \in EvictUnion  BY <5>2
          <5>4. s2 = self  BY <3>4, <4>1, <5>3
          <5>. QED  BY <4>3, <5>4
        <4>. QED  BY <4>2, <4>3
      <3>. QED  BY <3>14, <3>15, <3>16
    <2>4. CASE flush(self)
      \* Three sub-cases of flush:
      \*   (A) ei[self] <= K+L, inner-then: `table[mod(ei,K)] := lo'[self]
      \*       * (-1)' -- |table[.]| is preserved, so `NoDupsTable' survives
      \*       unchanged.  FULLY DISCHARGED with the help of `EiType'
      \*       (needed to pin `mod(ei[self], K) \in 1..K').
      \*   (B) ei[self] <= K+L, inner-else: UNCHANGED table/newexternal
      \*       (FULLY DISCHARGED below);
      \*   (C) ei[self] >  K+L, outer-else: flush loop exits, pc'[self]
      \*       becomes "rtrn" (in the third conjunct's trigger set).
      \*       Discharging this requires `NoDupsTable' at pc=flush',
      \*       which in turn requires carrying `NoDupsTable' through
      \*       the insertion-sort body (a multiset-permutation
      \*       invariant -- see doc-comment (b)/(c)).  OMITTED.
      <3>. USE <2>4 DEF flush
      <3>1. CASE ~(ei[self] <= K+L)
        \* (C) outer-else: the flush loop exits.  table UNCHANGED,
        \* evict UNCHANGED, pc'[self] = "rtrn".
        \*
        \* TableType' and FindOrPut' => NoDupsTable' close directly
        \* (via UNCHANGED table / UNCHANGED evict + EvictExclusive).
        \* The third conjunct triggers at self (pc'[self] = "rtrn")
        \* and reduces to `NoDupsTable' at pre-state; self is at
        \* pc[self] = "flush", which is NOT in the pre-state trigger
        \* set {"rtrn","endEv"}.  So we need NoDupsTable to already
        \* hold at pc = "flush", which requires carrying it through
        \* the insertion-sort body (sort-permutation invariant --
        \* see doc-comment (b)/(c)).  That single sub-step is OMITTED
        \* below; all other set-case reasoning is discharged here.
        <4>. USE <3>1, ProcSetIsWriter
             DEF EvictExclusive, EvictUnion, EvictLabels
        <4>1. UNCHANGED <<table, evict>>
          BY <3>1
        <4>2. pc[self] = "flush"  OBVIOUS
        <4>3. pc[self] \in EvictUnion  BY <4>2
        <4>4. evict = TRUE  BY <4>3
        <4>5. evict' = TRUE  BY <4>1, <4>4
        <4>6. pc'[self] = "rtrn"  BY <3>1
        <4>7. \A s2 \in ProcSet : s2 # self => pc'[s2] = pc[s2]
          BY <3>1
        <4>8. TableType'
          BY <4>1
        <4>9. FindOrPut' => NoDupsTable'
          <5>. SUFFICES ASSUME FindOrPut'  PROVE NoDupsTable'
            OBVIOUS
          <5>1. evict' = FALSE  BY DEF FindOrPut
          <5>. QED  BY <4>5, <5>1
        \* Third conjunct: table UNCHANGED, so NoDupsTable' <=> NoDupsTable.
        \* Need NoDupsTable at pre-state.  At s2 # self, pc'[s2] = pc[s2];
        \* if pc[s2] \in {"rtrn","endEv"}, by EvictExclusive mutex with
        \* self \in EvictUnion we get s2 = self, contradiction.  At
        \* s2 = self, pc'[self] = "rtrn" triggers and we reduce to the
        \* OMITTED sub-step `NoDupsTable at pc[self] = "flush"'.
        <4>10. NoDupsTable  \* OMITTED sort-permutation invariant
          OMITTED
        <4>11. NoDupsTable'
          BY <4>1, <4>10
        <4>12. \A s2 \in ProcSet :
                  pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
          BY <4>11
        <4>. QED  BY <4>8, <4>9, <4>12
      <3>2. CASE ei[self] <= K+L
        <4>1. CASE ~( lo'[self] # empty
                     /\ lo'[self] > largestElem(newexternal)
                     /\ ((ei[self] <= K /\ ~wrapped(lo'[self], ei[self]))
                         \/ (ei[self] >  K /\  wrapped(lo'[self], ei[self]))))
          \* (B) inner-else: UNCHANGED table/newexternal, pc'[self] stays
          \* "flush", evict unchanged.
          <5>1. UNCHANGED <<table, newexternal>>
            BY <3>2, <4>1
          <5>2. table' = table
            BY <5>1
          <5>3. evict' = evict
            OBVIOUS
          <5>4. pc'[self] = "flush"
            BY <3>2
          <5>5. \A s2 \in ProcSet : s2 # self => pc'[s2] = pc[s2]
            BY <3>2
          <5>6. TableType'  BY <5>2
          <5>7. FindOrPut' => NoDupsTable'
            <6>. SUFFICES ASSUME FindOrPut'  PROVE NoDupsTable'
              OBVIOUS
            <6>1. FindOrPut  BY <5>3
            <6>. QED  BY <5>2, <6>1
          <5>8. \A s2 \in ProcSet :
                  pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
            <6>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                  pc'[s2] \in {"rtrn", "endEv"}
                          PROVE  NoDupsTable'
              OBVIOUS
            <6>1. CASE s2 = self
              BY <5>4, <6>1
            <6>2. CASE s2 # self
              <7>1. pc'[s2] = pc[s2]  BY <5>5, <6>2
              <7>. QED  BY <5>2, <7>1
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <5>6, <5>7, <5>8
        <4>2. CASE lo'[self] # empty
                   /\ lo'[self] > largestElem(newexternal)
                   /\ ((ei[self] <= K /\ ~wrapped(lo'[self], ei[self]))
                       \/ (ei[self] >  K /\  wrapped(lo'[self], ei[self])))
          \* (A) inner-then: `table[mod(ei, K)] := lo'[self] * (-1)'.
          \* The mutation preserves |cell|, so NoDupsTable is preserved.
          \* We use `EiType' to pin `pos = mod(ei[self], K) \in 1..K'
          \* and `DOMAIN lo = ProcSet' to reduce `[lo EXCEPT ...][self]'.
          <5>. DEFINE pos == mod(ei[self], K)
          <5>0. lo' = [lo EXCEPT ![self] = table[pos]]
            BY <3>2
          <5>1. lo'[self] = table[pos]
            BY <5>0
          <5>2. table' = [table EXCEPT ![pos] = lo'[self] * (-1)]
            BY <3>2, <4>2
          <5>3. ei'[self] = ei[self] + 1
            BY <3>2
          <5>4. pc'[self] = "flush"
            BY <3>2
          <5>5. evict' = evict
            OBVIOUS
          <5>6. \A s2 \in ProcSet : s2 # self => pc'[s2] = pc[s2]
            BY <3>2
          \* Establish pos \in 1..K via EiType + OAAssumption.
          <5>7. ei[self] \in Nat
            OBVIOUS
          <5>8. K \in Nat \ {0}
            BY OAAssumption
          <5>9. ei[self] % K \in 0 .. (K - 1)
            BY <5>7, <5>8
          <5>10. pos \in 1..K
            BY <5>8, <5>9 DEF mod
          \* Typing of the cell we are overwriting.
          <5>11. lo'[self] \in TableValues
            BY <5>1, <5>10
          <5>12. lo'[self] \in fps \cup NegFps
            BY <5>11, <4>2
          <5>13. lo'[self] \in Int
            <6>1. CASE lo'[self] \in fps
              BY <6>1, OAAssumption
            <6>2. CASE lo'[self] \in NegFps
              <7>. PICK f \in fps : lo'[self] = -f
                BY <6>2 DEF NegFps
              <7>1. f \in Nat \ {0}  BY OAAssumption
              <7>. QED  BY <7>1
            <6>. QED  BY <5>12, <6>1, <6>2
          <5>14. lo'[self] * (-1) \in fps \cup NegFps
            <6>1. CASE lo'[self] \in fps
              <7>1. lo'[self] \in Nat \ {0}  BY <6>1, OAAssumption
              <7>2. lo'[self] * (-1) = -lo'[self]
                BY <7>1
              <7>3. -lo'[self] \in NegFps
                BY <6>1 DEF NegFps
              <7>. QED  BY <7>2, <7>3
            <6>2. CASE lo'[self] \in NegFps
              <7>. PICK f \in fps : lo'[self] = -f
                BY <6>2 DEF NegFps
              <7>1. f \in Nat \ {0}  BY OAAssumption
              <7>2. lo'[self] * (-1) = f
                BY <7>1
              <7>. QED  BY <7>2
            <6>. QED  BY <5>12, <6>1, <6>2
          <5>15. TableType'
            <6>. SUFFICES ASSUME NEW j \in 1..K
                          PROVE  table'[j] \in TableValues
              BY <5>2
            <6>1. CASE j = pos
              <7>1. table'[j] = lo'[self] * (-1)
                BY <5>2, <5>10, <6>1
              <7>2. lo'[self] * (-1) \in TableValues
                BY <5>14
              <7>. QED  BY <7>1, <7>2
            <6>2. CASE j # pos
              <7>1. table'[j] = table[j]
                BY <5>2, <5>10, <6>2
              <7>. QED  BY <7>1
            <6>. QED  BY <6>1, <6>2
          \* abs preservation at each cell.
          <5>16. \A j \in 1..K : abs(table'[j]) = abs(table[j])
            <6>. SUFFICES ASSUME NEW j \in 1..K
                          PROVE  abs(table'[j]) = abs(table[j])
              OBVIOUS
            <6>1. CASE j = pos
              <7>1. table'[j] = lo'[self] * (-1)
                BY <5>2, <5>10, <6>1
              <7>2. table[j] = lo'[self]
                BY <5>1, <6>1
              <7>3. abs(lo'[self] * (-1)) = abs(lo'[self])
                BY <5>13 DEF abs
              <7>. QED  BY <7>1, <7>2, <7>3
            <6>2. CASE j # pos
              <7>1. table'[j] = table[j]
                BY <5>2, <5>10, <6>2
              <7>. QED  BY <7>1
            <6>. QED  BY <6>1, <6>2
          \* Forward non-emptiness: if table'[j] # empty then table[j] # empty.
          <5>17. \A j \in 1..K : table'[j] # empty => table[j] # empty
            <6>. SUFFICES ASSUME NEW j \in 1..K, table'[j] # empty
                          PROVE  table[j] # empty
              OBVIOUS
            <6>1. CASE j = pos
              \* table[pos] = lo'[self] # empty by the CASE hypothesis.
              BY <5>1, <4>2, <6>1
            <6>2. CASE j # pos
              <7>1. table'[j] = table[j]
                BY <5>2, <5>10, <6>2
              <7>. QED  BY <7>1
            <6>. QED  BY <6>1, <6>2
          <5>18. NoDupsTable => NoDupsTable'
            <6>. SUFFICES ASSUME NoDupsTable,
                                  NEW i \in 1..K, NEW j \in 1..K,
                                  i # j,
                                  table'[i] # empty,
                                  table'[j] # empty
                          PROVE  abs(table'[i]) # abs(table'[j])
              OBVIOUS
            <6>1. table[i] # empty /\ table[j] # empty
              BY <5>17
            <6>2. abs(table[i]) # abs(table[j])
              BY <6>1
            <6>. QED  BY <5>16, <6>2
          <5>19. FindOrPut' => NoDupsTable'
            <6>. SUFFICES ASSUME FindOrPut'  PROVE NoDupsTable'
              OBVIOUS
            <6>1. FindOrPut  BY <5>5
            <6>2. NoDupsTable  BY <6>1
            <6>. QED  BY <6>2, <5>18
          <5>20. \A s2 \in ProcSet :
                    pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
            <6>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                  pc'[s2] \in {"rtrn", "endEv"}
                          PROVE  NoDupsTable'
              OBVIOUS
            <6>1. CASE s2 = self
              <7>1. pc'[self] = "flush"  BY <5>4
              <7>. QED  BY <6>1, <7>1
            <6>2. CASE s2 # self
              <7>1. pc'[s2] = pc[s2]  BY <5>6, <6>2
              <7>2. pc[s2] \in {"rtrn", "endEv"}  BY <7>1
              <7>3. NoDupsTable  BY <7>2
              <7>. QED  BY <7>3, <5>18
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <5>15, <5>19, <5>20
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>2
    <2>5. CASE rtrn(self)
      \* rtrn: table UNCHANGED, evict UNCHANGED, pc'[self] = Head(stack[
      \* self]).pc.  By DupInv's third conjunct, NoDupsTable held pre,
      \* so it still holds post regardless of which pc value was popped.
      <3>. USE <2>5 DEF rtrn
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'
        BY <3>1
      <3>3. FindOrPut' => NoDupsTable'
        BY <3>1
      <3>4. NoDupsTable
        BY DEF DupInv
      <3>5. NoDupsTable'
        BY <3>1, <3>4
      <3>6. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        BY <3>5
      <3>. QED  BY <3>2, <3>3, <3>6
    <2>. QED  BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Evict
  (***********************************************************************)
  (* Writer body disjuncts.                                                *)
  (***********************************************************************)
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  DupInv'
    <2>1. CASE pick(self)
      <3>. USE <2>1 DEF pick
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"Done", "put"}
            OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>2. CASE put(self)
      <3>. USE <2>2 DEF put
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"waitEv", "chkSnc"}
            OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>3. CASE waitEv(self)
      <3>. USE <2>3 DEF waitEv
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] = "endWEv"  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>4. CASE endWEv(self)
      <3>. USE <2>4 DEF endWEv
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] = "put"  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>5. CASE chkSnc(self)
      <3>. USE <2>5 DEF chkSnc
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"cntns", "insrt"}  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>6. CASE cntns(self)
      <3>. USE <2>6 DEF cntns
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"pick", "onSnc", "cntns"}  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>7. CASE onSnc(self)
      <3>. USE <2>7 DEF onSnc
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"pick", "insrt"}  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>8. CASE insrt(self)
      <3>. USE <2>8 DEF insrt
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"cas", "isMth", "tryEv"}  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>9. CASE isMth(self)
      <3>. USE <2>9 DEF isMth
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"pick", "insrt"}  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>10. CASE cas(self)
      \* The only writer disjunct that may mutate `table'.  Split on the
      \* CAS compare: failed-CAS (the 1st-IF ELSE branch) leaves `table'
      \* UNCHANGED and, using `ResultType' to determine that the 2nd-IF
      \* fires its ELSE branch, yields `pc'[self] = "insrt"'.  The three
      \* `DupInv' conjuncts all reduce to their pre-state counterparts.
      \* Successful-CAS (1st-IF THEN) writes `fp[self]' at the probe slot
      \* and is the deep case -- see doc-comment (a).
      <3>. USE <2>10 DEF cas
      <3>1. CASE ~(table[idx(fp[self],index[self])] = expected[self])
        \* Failed CAS.
        <4>1. table' = table
          BY <3>1
        <4>2. result' = [result EXCEPT ![self] = FALSE]
          BY <3>1
        <4>3. self \in DOMAIN result
          BY ProcSetIsWriter
        <4>4. result'[self] = FALSE
          BY <4>2, <4>3
        <4>5. pc'[self] = "insrt"
          BY <4>4
        <4>6. evict' = evict
          OBVIOUS
        <4>7. TableType'
          BY <4>1
        <4>8. FindOrPut' => NoDupsTable'
          <5>. SUFFICES ASSUME FindOrPut'  PROVE NoDupsTable'
            OBVIOUS
          <5>1. FindOrPut  BY <4>6
          <5>. QED  BY <4>1, <5>1
        <4>9. \A s2 \in ProcSet :
                pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"rtrn", "endEv"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. CASE s2 = self
            BY <4>5, <5>1
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <4>4, <5>2
            <6>. QED  BY <4>1, <6>1
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>7, <4>8, <4>9
      <3>2. CASE table[idx(fp[self],index[self])] = expected[self]
        \* Successful CAS.  The new cell's `abs(fp[self])' must avoid
        \* collision with any other non-empty cell -- the central
        \* probe-sequence correctness invariant for open addressing.
        \* That is the genuinely deep case left OMITTED here.
        OMITTED
      <3>. QED  BY <3>1, <3>2
    <2>11. CASE tryEv(self)
      \* tryEv may flip `evict' to TRUE, in which case `FindOrPut'' is
      \* FALSE and the second conjunct is vacuous.  Either way `table'
      \* is UNCHANGED and `pc'[self] \in {"waitIns", "put"}'.
      <3>. USE <2>11 DEF tryEv
      <3>1. UNCHANGED table
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'
        \* If FindOrPut' (evict' = FALSE), then we're in the ELSE branch
        \* (evict was TRUE pre).  evict' = evict, FindOrPut held pre,
        \* NoDupsTable held pre, table unchanged so NoDupsTable' holds.
        <4>. SUFFICES ASSUME FindOrPut'  PROVE NoDupsTable'
          OBVIOUS
        <4>1. evict = TRUE \/ evict = FALSE
          OBVIOUS
        <4>2. CASE evict = FALSE
          \* THEN branch fired: evict' = TRUE, contradicting FindOrPut'.
          <5>1. evict' = TRUE  BY <4>2
          <5>2. ~FindOrPut'  BY <5>1
          <5>. QED  BY <5>2
        <4>3. CASE evict = TRUE
          \* ELSE branch fired: evict' = evict = TRUE, contradicting FindOrPut'.
          <5>1. evict' = evict  BY <4>3
          <5>2. evict' = TRUE  BY <4>3, <5>1
          <5>3. ~FindOrPut'  BY <5>2
          <5>. QED  BY <5>3
        <4>. QED  BY <4>1, <4>2, <4>3
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] \in {"waitIns", "put"}  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>12. CASE waitIns(self)
      <3>. USE <2>12 DEF waitIns
      <3>1. UNCHANGED <<table, evict>>
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. FindOrPut' => NoDupsTable'  BY <3>1
      <3>4. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"rtrn", "endEv"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          <5>1. pc'[self] = "strIns"  OBVIOUS
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>. QED  BY <5>1, <3>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>13. CASE endEv(self)
      \* The pivotal transition: evict' = FALSE, so FindOrPut' becomes
      \* TRUE.  The post-flush pc invariant of DupInv (third conjunct)
      \* gives us NoDupsTable from pc[self] = "endEv" pre.
      <3>. USE <2>13 DEF endEv
      <3>1. UNCHANGED table
        OBVIOUS
      <3>2. TableType'  BY <3>1
      <3>3. NoDupsTable
        BY DEF DupInv
      <3>4. NoDupsTable'
        BY <3>1, <3>3
      <3>5. FindOrPut' => NoDupsTable'
        BY <3>4
      <3>6. \A s2 \in ProcSet :
              pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
        BY <3>4
      <3>. QED  BY <3>2, <3>5, <3>6
    <2>. QED  BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8,
                  <2>9, <2>10, <2>11, <2>12, <2>13 DEF p
  (***********************************************************************)
  (* Terminating: vars unchanged.                                          *)
  (***********************************************************************)
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* DupInv => Duplicates.                                                   *)
(*                                                                         *)
(* `Duplicates' is `FindOrPut => P(SelectSeq(table, e # empty))', so under *)
(* `FindOrPut' (= `evict = FALSE'), we apply `SelectSeqAbsDistinct' to     *)
(* the index-form `NoDupsTable' supplied by the second conjunct of        *)
(* DupInv.  The `Len(sub) < 2 THEN TRUE' branch of `Duplicates' is        *)
(* trivially handled by the universal quantifier becoming vacuous.       *)
(***************************************************************************)
LEMMA DupInvImpliesDuplicates == DupInv => Duplicates
  <1>. SUFFICES ASSUME DupInv, FindOrPut
                PROVE  LET sub == SelectSeq(table, LAMBDA e : e # empty)
                       IN IF Len(sub) < 2 THEN TRUE
                          ELSE \A i \in 1..(Len(sub) - 1) :
                                 \A j \in (i+1)..Len(sub) :
                                    abs(sub[i]) # abs(sub[j])
    BY DEF Duplicates, FindOrPut
  <1>. USE DEF DupInv, TableType, NoDupsTable
  <1>1. table \in [1..K -> TableValues]
    OBVIOUS
  <1>2. \A i, j \in 1..K : i # j /\ table[i] # empty /\ table[j] # empty
            => abs(table[i]) # abs(table[j])
    OBVIOUS
  <1>3. LET sub == SelectSeq(table, LAMBDA e : e # empty)
        IN \A i \in 1..(Len(sub) - 1) :
             \A j \in (i+1)..Len(sub) :
                 abs(sub[i]) # abs(sub[j])
    BY <1>1, <1>2, SelectSeqAbsDistinct
  <1>. QED  BY <1>3

(***************************************************************************)
(* Main safety theorem: Spec implies []Duplicates.                         *)
(*                                                                         *)
(* `DupInv' is proved inductive in conjunction with `Inv', `StackOK'       *)
(* (required by `InvNext's `rtrn' case), `ResultType' (required by the    *)
(* failed-CAS branch of `DupInvNext'), and `EiType' (required by the      *)
(* flush inner-then branch of `DupInvNext'), so the PTL chain proves      *)
(* `Spec => [](Inv /\ StackOK /\ ResultType /\ EiType /\ DupInv)'.         *)
(***************************************************************************)
THEOREM DuplicatesSafety == Spec => []Duplicates
  <1>1. Spec => [](Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                   /\ LoType /\ EvictExclusive /\ DupInv)
    <2>1. Init => Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                    /\ LoType /\ EvictExclusive /\ DupInv
      BY InitInv, InitStackOK, InitResultType, InitEiType, InitEjType,
         InitLoType, InitEvictExclusive, InitDupInv
    <2>2. (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
             /\ LoType /\ EvictExclusive /\ DupInv) /\ [Next]_vars
            => (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                  /\ LoType /\ EvictExclusive /\ DupInv)'
      <3>1. Inv /\ StackOK /\ [Next]_vars => Inv'
        BY InvNext
      <3>2. Inv /\ StackOK /\ [Next]_vars => StackOK'
        BY StackOKInd
      <3>3. ResultType /\ [Next]_vars => ResultType'
        BY ResultTypeInd
      <3>4. StackOK /\ EiType /\ [Next]_vars => EiType'
        BY EiTypeInd
      <3>5. StackOK /\ EiType /\ EjType /\ [Next]_vars => EjType'
        BY EjTypeInd
      <3>6. Inv /\ StackOK /\ EiType /\ DupInv /\ LoType /\ [Next]_vars
              => LoType'
        BY LoTypeInd
      <3>7. Inv /\ StackOK /\ EvictExclusive /\ [Next]_vars => EvictExclusive'
        BY EvictExclusiveInd
      <3>8. Inv /\ ResultType /\ EiType /\ EjType /\ LoType
              /\ EvictExclusive /\ DupInv /\ [Next]_vars => DupInv'
        BY DupInvNext
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
    <2>. QED  BY <2>1, <2>2, PTL DEF Spec
  <1>2. (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
           /\ LoType /\ EvictExclusive /\ DupInv) => Duplicates
    BY DupInvImpliesDuplicates
  <1>. QED  BY <1>1, <1>2, PTL

(***************************************************************************)
(*                                                                         *)
(*  REMAINING SAFETY PROPERTIES (left as OMITTED stubs).                   *)
(*                                                                         *)
(* The other top-level safety properties of OpenAddressing are genuine     *)
(* deep results about the algorithm's data structure.  They are stated     *)
(* below for completeness; their proofs would require strengthened         *)
(* invariants that we sketch in the comments but do not discharge here.    *)
(*                                                                         *)
(***************************************************************************)

(***************************************************************************)
(*                                                                         *)
(*  SORTEDNESS OF THE EXTERNAL STORAGE.                                    *)
(*                                                                         *)
(*  We prove `Spec => []Sorted' via a strengthened invariant `SortedInv'   *)
(*  carrying both well-typing (`external, newexternal \in Seq(fps)') and   *)
(*  the strict-ascending property of the underlying sequences.  From       *)
(*  `SortedInv' we recover the stated `Sorted' property by observing that  *)
(*  no element of either sequence equals `empty' (`empty \notin fps' is    *)
(*  the spec's top-level assumption), so `SelectSeq(seq, e # empty) = seq' *)
(*  and the strict-ascending check on `seq' becomes the body of            *)
(*  `isSorted(seq)'.                                                       *)
(*                                                                         *)
(*  The genuinely deep sub-results are sequence-theoretic facts about      *)
(*  `SelectSeq', concatenation, and `Append'; we state them as lemmas      *)
(*  with `OMITTED' proofs.                                                 *)
(*                                                                         *)
(***************************************************************************)

(***************************************************************************)
(* Strict-ascending predicate on a sequence (of integers).                 *)
(***************************************************************************)
StrAsc(s) == \A i \in 1..(Len(s) - 1) : s[i] < s[i+1]

(***************************************************************************)
(* The strengthened invariant.                                             *)
(***************************************************************************)
SortedInv ==
  /\ external    \in Seq(fps)
  /\ newexternal \in Seq(fps)
  /\ StrAsc(external)
  /\ StrAsc(newexternal)

(***************************************************************************)
(* Sequence-theoretic helper lemmas.  These are general-purpose facts     *)
(* about `SelectSeq', `\o', and `Append' that are not part of the         *)
(* TLAPS standard library and would require recursive function-level     *)
(* induction to discharge.  We state them here and leave the proofs as    *)
(* `OMITTED'.                                                              *)
(***************************************************************************)

\* SelectSeq filtering on a sequence of fps with `e # empty' is the       
\* identity (because `empty \notin fps').                                  
LEMMA SelectSeqIdentityOnFps ==
  ASSUME NEW s \in Seq(fps)
  PROVE  SelectSeq(s, LAMBDA e : e # empty) = s
  OMITTED

\* SelectSeq of a sequence in Seq(fps) is again in Seq(fps).
LEMMA SelectSeqInSeqFps ==
  ASSUME NEW s \in Seq(fps), NEW Test(_)
  PROVE  SelectSeq(s, Test) \in Seq(fps)
  OMITTED

\* SelectSeq preserves strict-ascending order.
LEMMA SelectSeqPreservesStrAsc ==
  ASSUME NEW s \in Seq(fps), StrAsc(s), NEW Test(_)
  PROVE  StrAsc(SelectSeq(s, Test))
  OMITTED

\* Range-bound for SelectSeq under a threshold predicate.
LEMMA SelectSeqStrictlyGreater ==
  ASSUME NEW s \in Seq(fps), NEW lower \in Int
  PROVE  \A i \in 1..Len(SelectSeq(s, LAMBDA p : p > lower)) :
            SelectSeq(s, LAMBDA p : p > lower)[i] > lower
  OMITTED

\* Range-bound for SelectSeq under a window predicate.
LEMMA SelectSeqInWindow ==
  ASSUME NEW s \in Seq(fps), NEW lower \in Int, NEW upper \in Int
  PROVE  \A i \in 1..Len(SelectSeq(s, LAMBDA p : p < upper /\ p > lower)) :
           /\ SelectSeq(s, LAMBDA p : p < upper /\ p > lower)[i] > lower
           /\ SelectSeq(s, LAMBDA p : p < upper /\ p > lower)[i] < upper
  OMITTED

(***************************************************************************)
(* Indexing into a concatenation.  This is the key sequence-theoretic     *)
(* fact missing from SequenceTheorems; we derive it via SubSeqOfConcat1 / *)
(* SubSeqOfConcat2 and SubSeqProperties.                                   *)
(***************************************************************************)
LEMMA ConcatIndex ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         NEW i \in 1..(Len(s) + Len(t))
  PROVE  (s \o t)[i] = IF i <= Len(s) THEN s[i] ELSE t[i - Len(s)]
  <1>1. Len(s \o t) = Len(s) + Len(t)
    BY ConcatProperties
  <1>2. s \o t \in Seq(S)
    BY ConcatProperties
  <1>3. Len(s) \in Nat  BY LenProperties
  <1>4. Len(t) \in Nat  BY LenProperties
  <1>5. SubSeq(s \o t, i, i) = <<(s \o t)[i]>>
    BY <1>1, <1>2, SubSeqProperties
  <1>6. CASE i <= Len(s)
    <2>1. i \in 1..Len(s)
      BY <1>6
    <2>2. SubSeq(s \o t, i, i) = SubSeq(s, i, i)
      BY <2>1, SubSeqOfConcat1
    <2>3. SubSeq(s, i, i) = <<s[i]>>
      BY <2>1, SubSeqProperties
    <2>4. <<(s \o t)[i]>> = <<s[i]>>
      BY <1>5, <2>2, <2>3
    <2>. QED  BY <2>4, <1>6
  <1>7. CASE i > Len(s)
    <2>1. i \in Len(s) + 1 .. Len(s) + Len(t)
      BY <1>7, <1>3, <1>4
    <2>2. SubSeq(s \o t, i, i) = SubSeq(t, i - Len(s), i - Len(s))
      BY <2>1, SubSeqOfConcat2
    <2>3. i - Len(s) \in 1..Len(t)
      BY <1>7, <1>3, <1>4, <2>1
    <2>4. SubSeq(t, i - Len(s), i - Len(s)) = <<t[i - Len(s)]>>
      BY <2>3, SubSeqProperties
    <2>5. <<(s \o t)[i]>> = <<t[i - Len(s)]>>
      BY <1>5, <2>2, <2>4
    <2>. QED  BY <2>5, <1>7
  <1>. QED  BY <1>6, <1>7

\* Concatenation preserves strict-ascending order when the boundary holds.
LEMMA ConcatStrAsc ==
  ASSUME NEW s1 \in Seq(Int), NEW s2 \in Seq(Int),
         StrAsc(s1), StrAsc(s2),
         s1 = <<>> \/ s2 = <<>> \/ s1[Len(s1)] < s2[1]
  PROVE  StrAsc(s1 \o s2)
  <1>. DEFINE c == s1 \o s2
  <1>1. Len(c) = Len(s1) + Len(s2)
    BY ConcatProperties
  <1>2. c \in Seq(Int)
    BY ConcatProperties
  <1>3. Len(s1) \in Nat  BY LenProperties
  <1>4. Len(s2) \in Nat  BY LenProperties
  <1>. SUFFICES ASSUME NEW i \in 1..(Len(c) - 1)
                PROVE  c[i] < c[i+1]
    BY DEF StrAsc
  <1>5. i \in 1..(Len(s1) + Len(s2))
    BY <1>1, <1>3, <1>4
  <1>6. i + 1 \in 1..(Len(s1) + Len(s2))
    BY <1>1, <1>3, <1>4
  <1>7. c[i] = IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]
    BY <1>5, ConcatIndex
  <1>8. c[i+1] = IF i+1 <= Len(s1) THEN s1[i+1] ELSE s2[i+1 - Len(s1)]
    BY <1>6, ConcatIndex
  <1>9. CASE i + 1 <= Len(s1)
    \* Both i and i+1 land in s1.
    <2>1. i <= Len(s1)
      BY <1>9
    <2>2. c[i] = s1[i]
      BY <1>7, <2>1
    <2>3. c[i+1] = s1[i+1]
      BY <1>8, <1>9
    <2>4. i \in 1..(Len(s1) - 1)
      BY <1>9, <1>3, <1>4
    <2>5. s1[i] < s1[i+1]
      BY <2>4 DEF StrAsc
    <2>. QED  BY <2>2, <2>3, <2>5
  <1>10. CASE i <= Len(s1) /\ ~(i + 1 <= Len(s1))
    \* Boundary: i = Len(s1), i+1 = Len(s1)+1.
    <2>1. i = Len(s1)
      BY <1>10, <1>3, <1>4
    <2>2. c[i] = s1[Len(s1)]
      BY <1>7, <1>10, <2>1
    <2>3. i + 1 - Len(s1) = 1
      BY <2>1
    <2>4. c[i+1] = s2[1]
      BY <1>8, <1>10, <2>3
    \* At the boundary we must have s1 # <<>> (since i >= 1 and i = Len(s1))
    \* and s2 # <<>> (since i+1 = Len(s1)+1 <= Len(c)-1+1 = Len(s1)+Len(s2),
    \* so Len(s2) >= 1).
    <2>5. s1 # <<>>
      <3>. SUFFICES ASSUME s1 = <<>>  PROVE FALSE
        OBVIOUS
      <3>1. Len(s1) = 0
        BY EmptySeq
      <3>2. i = 0
        BY <2>1, <3>1
      <3>. QED  BY <3>2
    <2>6. s2 # <<>>
      <3>. SUFFICES ASSUME s2 = <<>>  PROVE FALSE
        OBVIOUS
      <3>1. Len(s2) = 0
        BY EmptySeq
      <3>2. Len(c) = Len(s1)
        BY <1>1, <3>1
      <3>3. i \in 1..(Len(s1) - 1)
        BY <3>2
      <3>4. i + 1 <= Len(s1)
        BY <3>3, <1>3
      <3>. QED  BY <3>4, <1>10
    <2>7. s1[Len(s1)] < s2[1]
      BY <2>5, <2>6
    <2>. QED  BY <2>2, <2>4, <2>7
  <1>11. CASE i > Len(s1)
    \* Both i and i+1 land in s2.
    <2>1. ~(i <= Len(s1))
      BY <1>11
    <2>2. ~(i + 1 <= Len(s1))
      BY <1>11
    <2>3. c[i] = s2[i - Len(s1)]
      BY <1>7, <2>1
    <2>4. c[i+1] = s2[i + 1 - Len(s1)]
      BY <1>8, <2>2
    <2>5. i - Len(s1) \in 1..(Len(s2) - 1)
      BY <1>11, <1>1, <1>3, <1>4
    <2>6. (i - Len(s1)) + 1 = i + 1 - Len(s1)
      OBVIOUS
    <2>7. s2[i - Len(s1)] < s2[(i - Len(s1)) + 1]
      BY <2>5 DEF StrAsc
    <2>. QED  BY <2>3, <2>4, <2>6, <2>7
  <1>. QED  BY <1>9, <1>10, <1>11, <1>3, <1>4

\* Append preserves strict-ascending order when the appended element is
\* strictly greater than the current last element (or the sequence is
\* empty).
LEMMA AppendStrAsc ==
  ASSUME NEW s \in Seq(Int), NEW elt \in Int,
         StrAsc(s),
         s = <<>> \/ s[Len(s)] < elt
  PROVE  StrAsc(Append(s, elt))
  <1>. DEFINE ap == Append(s, elt)
  <1>1. ap \in Seq(Int)
    BY AppendProperties
  <1>2. Len(ap) = Len(s) + 1
    BY AppendProperties
  <1>3. \A i \in 1..Len(s) : ap[i] = s[i]
    BY AppendProperties
  <1>4. ap[Len(s) + 1] = elt
    BY AppendProperties
  <1>5. Len(s) \in Nat
    BY LenProperties
  <1>. SUFFICES ASSUME NEW i \in 1..(Len(ap) - 1)
                PROVE  ap[i] < ap[i+1]
    BY DEF StrAsc
  <1>6. i \in 1..Len(s)
    BY <1>2, <1>5
  <1>7. ap[i] = s[i]
    BY <1>3, <1>6
  <1>8. CASE i < Len(s)
    <2>1. i+1 \in 1..Len(s)
      BY <1>6, <1>8, <1>5
    <2>2. ap[i+1] = s[i+1]
      BY <1>3, <2>1
    <2>3. i \in 1..(Len(s) - 1)
      BY <1>6, <1>8, <1>5
    <2>4. s[i] < s[i+1]
      BY <2>3 DEF StrAsc
    <2>. QED  BY <1>7, <2>2, <2>4
  <1>9. CASE i = Len(s)
    <2>1. i + 1 = Len(s) + 1
      BY <1>9
    <2>2. ap[i+1] = elt
      BY <1>4, <2>1
    <2>3. s # <<>>
      \* If s = <<>>, Len(s) = 0, but i >= 1 and i = Len(s), contradiction.
      <3>. SUFFICES ASSUME s = <<>>  PROVE FALSE
        OBVIOUS
      <3>1. Len(s) = 0
        BY EmptySeq
      <3>2. i = 0
        BY <1>9, <3>1
      <3>3. i \in 1..(Len(ap) - 1)
        OBVIOUS
      <3>. QED  BY <3>2, <3>3, <1>2, <1>5
    <2>4. s[Len(s)] < elt
      BY <2>3
    <2>5. s[i] < elt
      BY <1>9, <2>4
    <2>. QED  BY <1>7, <2>2, <2>5
  <1>. QED  BY <1>6, <1>8, <1>9, <1>5

\* `SelectSeq' on the empty sequence is the empty sequence (for any
\* predicate).  This one is easy enough to discharge from the standard
\* definition of `SelectSeq' in the `Sequences' module.
LEMMA SelectSeqEmpty ==
  ASSUME NEW Test(_)
  PROVE  SelectSeq(<<>>, Test) = <<>>
  BY DEF SelectSeq

\* `largestElem' bounds: for any sequence in `Seq(fps)', the largest       
\* element is either `0' (when the sequence is empty) or `s[Len(s)]'.       
LEMMA LargestElemDef ==
  ASSUME NEW s \in Seq(fps)
  PROVE  largestElem(s) = IF s = <<>> THEN 0 ELSE s[Len(s)]
  BY DEF largestElem, last

(***************************************************************************)
(* Init implies SortedInv.                                                 *)
(***************************************************************************)
LEMMA InitSortedInv == Init => SortedInv
  <1>. SUFFICES ASSUME Init  PROVE SortedInv
    OBVIOUS
  <1>1. external = <<>>  /\  newexternal = <<>>
    BY DEF Init
  <1>2. <<>> \in Seq(fps)
    BY EmptySeq
  <1>3. external \in Seq(fps)
    BY <1>1, <1>2
  <1>4. newexternal \in Seq(fps)
    BY <1>1, <1>2
  <1>5. StrAsc(external)
    \* Len(<<>>) = 0, so the universal is over 1..(-1) = {} -- vacuous.
    <2>1. Len(external) = 0
      BY <1>1, EmptySeq
    <2>2. 1..(Len(external) - 1) = {}
      BY <2>1
    <2>. QED  BY <2>2 DEF StrAsc
  <1>6. StrAsc(newexternal)
    <2>1. Len(newexternal) = 0
      BY <1>1, EmptySeq
    <2>2. 1..(Len(newexternal) - 1) = {}
      BY <2>1
    <2>. QED  BY <2>2 DEF StrAsc
  <1>. QED  BY <1>3, <1>4, <1>5, <1>6 DEF SortedInv

(***************************************************************************)
(* Inductive step for SortedInv.                                           *)
(*                                                                         *)
(* Only the `flush' action of the `Evict' procedure mutates `external' or  *)
(* `newexternal'.  All writer-body actions and the other Evict labels      *)
(* leave both sequences UNCHANGED, in which case `SortedInv'' follows      *)
(* trivially from `SortedInv'.                                             *)
(*                                                                         *)
(* The `flush' action splits into three cases:                             *)
(*   (a) `ei[self] <= K+L', inner-if FALSE: UNCHANGED both sequences.      *)
(*   (b) `ei[self] <= K+L', inner-if TRUE: external UNCHANGED;             *)
(*       newexternal' = Append(newexternal \o subSeqSmaller(...), lo).     *)
(*       This case requires the SelectSeq + Concat + Append helper lemmas. *)
(*   (c) `ei[self] >  K+L': newexternal' = <<>>;                           *)
(*       external'    = newexternal \o subSeqLarger(external, newexternal).*)
(*       Requires Concat + SelectSeq helpers.                              *)
(*                                                                         *)
(* Case (c) -- the `outer-else' -- is fully discharged here from the       *)
(* generic SelectSeq / Concat / Append helper lemmas plus TLAPS'           *)
(* `SequenceTheorems!ConcatProperties' and `LargestElemDef' /              *)
(* `ElementOfSeq' to extract `largestElem(newexternal) = newexternal[Len]' *)
(* as a bona fide integer.                                                 *)
(*                                                                         *)
(* Case (b) -- the `inner-then' -- is FULLY DISCHARGED with the help of    *)
(* the layered invariants `EiType /\ DupInv' (the latter supplies          *)
(* `TableType').  The proof decomposes `lo'[self] \in fps' into:           *)
(*                                                                         *)
(*   (i)  `table[mod(ei[self], K)] \in fps \cup NegFps \cup {empty}':      *)
(*        `TableType' + `EiType' (for `mod(ei[self], K) \in 1..K').        *)
(*        Combined with the CASE's `lo'[self] # empty' this gives          *)
(*        `lo'[self] \in fps \cup NegFps'.                                 *)
(*                                                                         *)
(*   (ii) Positivity: `lo'[self] > largestElem(newexternal) >= 0'          *)
(*        (`largestElem' returns `0' on an empty sequence and an `fps'     *)
(*        element otherwise, which is strictly positive by OAAssumption).  *)
(*        Since every element of `NegFps' is strictly negative, we         *)
(*        exclude `NegFps' and conclude `lo'[self] \in fps'.               *)
(*                                                                         *)
(* The remainder of the proof (Seq(fps) and StrAsc for `newexternal'')     *)
(* follows the same SelectSeq + Concat + Append pattern as (c).            *)
(***************************************************************************)
LEMMA SortedInvNext ==
  EiType /\ DupInv /\ SortedInv /\ [Next]_vars => SortedInv'
  <1>. SUFFICES ASSUME EiType, DupInv, SortedInv, [Next]_vars
                PROVE  SortedInv'
    OBVIOUS
  <1>. USE DEF SortedInv, StrAsc, EiType,
              DupInv, TableType, TableValues, NegFps
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. ASSUME NEW self \in Writer, p(self)
        PROVE  SortedInv'
    \* Writer body: external and newexternal are UNCHANGED in every disjunct.
    BY <1>2 DEF p, pick, put, waitEv, endWEv, chkSnc, cntns, onSnc, insrt,
                isMth, cas, tryEv, waitIns, endEv
  <1>3. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  SortedInv'
    <2>1. CASE strIns(self)
      BY <2>1 DEF strIns
    <2>2. CASE nestedIns(self)
      BY <2>2 DEF nestedIns
    <2>3. CASE set(self)
      BY <2>3 DEF set
    <2>4. CASE rtrn(self)
      BY <2>4 DEF rtrn
    <2>5. CASE flush(self)
      \* The two outer cases are split by the IF condition (`ei[self] <= K+L'),
      \* using excluded middle so we do not need a typing invariant for `ei'.
      \* The genuinely deep sub-cases are discharged via the OMITTED helper
      \* lemmas above.
      <3>. USE <2>5 DEF flush
      <3>1. CASE ~(ei[self] <= K+L)
        \* Outer-else of the IF: external' = newexternal \o subSeqLarger(...);
        \* newexternal' = <<>>.
        <4>1. external' = newexternal \o subSeqLarger(external, newexternal)
          BY <3>1
        <4>2. newexternal' = <<>>
          BY <3>1
        <4>3. newexternal' \in Seq(fps)  /\  StrAsc(newexternal')
          <5>1. <<>> \in Seq(fps)  BY EmptySeq
          <5>2. Len(newexternal') = 0  BY <4>2, EmptySeq
          <5>3. 1..(Len(newexternal') - 1) = {}  BY <5>2
          <5>. QED  BY <4>2, <5>1, <5>3
        <4>4. external' \in Seq(fps)  /\  StrAsc(external')
          \* Let `sl == subSeqLarger(external, newexternal)'.  Two cases:
          \*
          \*  - newexternal = <<>>: then `sl = external', so external' =
          \*    <<>> \o external = external, which inherits Seq(fps) and
          \*    StrAsc directly from SortedInv.
          \*
          \*  - newexternal # <<>>: then `sl = SelectSeq(external,
          \*    LAMBDA p: p > largestElem(newexternal))'.  SelectSeqInSeqFps
          \*    and SelectSeqPreservesStrAsc (both generic sequence lemmas)
          \*    give `sl \in Seq(fps)' and `StrAsc(sl)'.  ConcatProperties
          \*    (TLAPS standard) then gives external' \in Seq(fps).  For
          \*    the strict-ascending property, if `sl = <<>>' we have
          \*    external' = newexternal.  Otherwise
          \*    `sl[1] > largestElem(newexternal) = newexternal[Len(newexternal)]'
          \*    (SelectSeqStrictlyGreater + LargestElemDef), so ConcatStrAsc's
          \*    boundary condition holds.
          <5>. DEFINE sl == subSeqLarger(external, newexternal)
          <5>0. external' = newexternal \o sl
            BY <4>1
          <5>a. fps \subseteq Int
            <6>1. fps \subseteq Nat \ {0}  BY OAAssumption
            <6>. QED  BY <6>1
          <5>b. newexternal \in Seq(Int)
            BY <5>a, SeqMonotonic
          <5>1. CASE newexternal = <<>>
            <6>1. sl = external
              BY <5>1 DEF subSeqLarger
            <6>2. external' = <<>> \o external
              BY <5>0, <5>1, <6>1
            <6>3. external' = external
              BY <6>2, ConcatEmptySeq
            <6>. QED  BY <6>3
          <5>2. CASE newexternal # <<>>
            <6>1. sl = SelectSeq(external, LAMBDA p : p > largestElem(newexternal))
              BY <5>2 DEF subSeqLarger
            <6>2. largestElem(newexternal) = newexternal[Len(newexternal)]
              <7>1. largestElem(newexternal) =
                      IF newexternal = <<>>
                         THEN 0
                         ELSE newexternal[Len(newexternal)]
                BY LargestElemDef
              <7>. QED  BY <5>2, <7>1
            <6>3. newexternal # <<>> /\ Len(newexternal) \in Nat \ {0}
              <7>1. Len(newexternal) \in Nat  BY LenProperties
              <7>2. Len(newexternal) # 0  BY <5>2, EmptySeq
              <7>. QED  BY <5>2, <7>1, <7>2
            <6>4. Len(newexternal) \in 1..Len(newexternal)
              BY <6>3
            <6>5. newexternal[Len(newexternal)] \in fps
              BY <6>4, ElementOfSeq
            <6>6. largestElem(newexternal) \in Int
              <7>1. newexternal[Len(newexternal)] \in Nat
                BY <6>5, OAAssumption
              <7>. QED  BY <6>2, <7>1
            <6>7. sl \in Seq(fps)
              BY <6>1, SelectSeqInSeqFps
            <6>8. StrAsc(sl)
              BY <6>1, SelectSeqPreservesStrAsc
            <6>9. \A i \in 1..Len(sl) : sl[i] > largestElem(newexternal)
              BY <6>1, <6>6, SelectSeqStrictlyGreater
            <6>10. external' \in Seq(fps)
              BY <5>0, <6>7, ConcatProperties
            <6>11. StrAsc(external')
              <7>1. CASE sl = <<>>
                <8>1. external' = newexternal \o <<>>
                  BY <5>0, <7>1
                <8>2. external' = newexternal
                  BY <8>1, ConcatEmptySeq
                <8>. QED  BY <8>2
              <7>2. CASE sl # <<>>
                <8>1. Len(sl) \in Nat /\ Len(sl) # 0
                  <9>1. Len(sl) \in Nat  BY <6>7, LenProperties
                  <9>2. Len(sl) # 0  BY <6>7, <7>2, EmptySeq
                  <9>. QED  BY <9>1, <9>2
                <8>2. 1 \in 1..Len(sl)
                  BY <8>1
                <8>3. sl[1] > largestElem(newexternal)
                  BY <6>9, <8>2
                <8>4. newexternal[Len(newexternal)] < sl[1]
                  BY <6>2, <6>6, <6>5, OAAssumption, <8>3
                <8>5. sl \in Seq(Int)
                  BY <5>a, <6>7, SeqMonotonic
                <8>. QED
                  BY <5>0, <5>b, <6>8, <8>4, <8>5, ConcatStrAsc
              <7>. QED  BY <7>1, <7>2
            <6>. QED  BY <6>10, <6>11
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>3, <4>4
      <3>2. CASE ei[self] <= K+L
        <4>1. external' = external
          BY <3>2
        <4>2. CASE ~( lo'[self] # empty
                    /\ lo'[self] > largestElem(newexternal)
                    /\ ((ei[self] <= K /\ ~wrapped(lo'[self], ei[self]))
                        \/ (ei[self] >  K /\  wrapped(lo'[self], ei[self]))))
          \* Inner-else: both UNCHANGED.
          <5>1. newexternal' = newexternal
            BY <3>2, <4>2
          <5>. QED  BY <4>1, <5>1
        <4>3. CASE /\ lo'[self] # empty
                   /\ lo'[self] > largestElem(newexternal)
                   /\ ((ei[self] <= K /\ ~wrapped(lo'[self], ei[self]))
                       \/ (ei[self] >  K /\  wrapped(lo'[self], ei[self])))
          \* Inner-then: external UNCHANGED;
          \*   newexternal' = Append(newexternal \o ss, lo'[self])
          \* where ss == subSeqSmaller(external, newexternal, lo'[self]).
          \*
          \* The main derivation is showing `lo'[self] \in fps':
          \*   - TableType + EiType + the CASE's `lo'[self] # empty'
          \*     give `lo'[self] \in fps \cup NegFps';
          \*   - `lo'[self] > largestElem(newexternal) >= 0' rules out
          \*     NegFps (whose elements are strictly negative).
          \* Once `lo'[self] \in fps' is available, the sequence-typing
          \* and strict-ascending properties of `newexternal'' follow
          \* from the generic `SelectSeq*', `ConcatStrAsc' and
          \* `AppendStrAsc' helpers.
          <5>. DEFINE ss  == subSeqSmaller(external, newexternal, lo'[self])
          <5>. DEFINE low == largestElem(newexternal)
          <5>. DEFINE hi  == lo'[self]
          <5>0. newexternal' = Append(newexternal \o ss, hi)
            BY <3>2, <4>3
          <5>ext. external' = external
            BY <4>1
          \*-----------------------------------------------------------
          \* (A) Derive hi \in fps.
          \*-----------------------------------------------------------
          <5>. DEFINE pos == mod(ei[self], K)
          <5>A1. lo' = [lo EXCEPT ![self] = table[pos]]
            BY <3>2
          <5>A2. DOMAIN lo = ProcSet
            OBVIOUS
          <5>A3. hi = table[pos]
            BY <5>A1, <5>A2
          <5>A4. ei[self] \in Nat
            OBVIOUS
          <5>A5. K \in Nat \ {0}
            BY OAAssumption
          <5>A6. ei[self] % K \in 0 .. (K - 1)
            BY <5>A4, <5>A5
          <5>A7. pos \in 1..K
            BY <5>A5, <5>A6 DEF mod
          <5>A8. hi \in TableValues
            BY <5>A3, <5>A7
          <5>A9. hi \in fps \cup NegFps
            BY <5>A8, <4>3
          <5>A10. fps \subseteq Nat \ {0}
            BY OAAssumption
          <5>A11. fps \subseteq Int
            BY <5>A10
          \* largestElem(newexternal) is a non-negative integer.
          <5>A12. low \in Nat
            <6>1. largestElem(newexternal) =
                    IF newexternal = <<>>
                       THEN 0 ELSE newexternal[Len(newexternal)]
              BY LargestElemDef
            <6>2. CASE newexternal = <<>>
              BY <6>1, <6>2
            <6>3. CASE newexternal # <<>>
              <7>1. Len(newexternal) \in Nat  BY LenProperties
              <7>2. Len(newexternal) # 0  BY <6>3, EmptySeq
              <7>3. Len(newexternal) \in 1..Len(newexternal)
                BY <7>1, <7>2
              <7>4. newexternal[Len(newexternal)] \in fps
                BY <7>3, ElementOfSeq
              <7>5. newexternal[Len(newexternal)] \in Nat
                BY <7>4, <5>A10
              <7>. QED  BY <6>1, <6>3, <7>5
            <6>. QED  BY <6>2, <6>3
          <5>A13. hi > low
            BY <4>3
          \* NegFps values are strictly negative.
          <5>A14. \A n \in NegFps : n < 0
            <6>. SUFFICES ASSUME NEW n \in NegFps
                          PROVE  n < 0
              OBVIOUS
            <6>1. PICK f \in fps : n = -f
              BY DEF NegFps
            <6>2. f \in Nat \ {0}
              BY <6>1, OAAssumption
            <6>. QED  BY <6>1, <6>2
          <5>A15. hi \notin NegFps
            <6>. SUFFICES ASSUME hi \in NegFps  PROVE FALSE
              OBVIOUS
            <6>1. hi < 0
              BY <5>A14
            <6>2. hi \in Int
              <7>1. PICK f \in fps : hi = -f  BY DEF NegFps
              <7>2. f \in Nat \ {0}  BY OAAssumption
              <7>. QED  BY <7>1, <7>2
            <6>3. low \in Int
              BY <5>A12
            <6>. QED  BY <5>A12, <5>A13, <6>1, <6>2, <6>3
          <5>A16. hi \in fps
            BY <5>A9, <5>A15
          <5>A17. hi \in Int
            BY <5>A16, <5>A11
          \*-----------------------------------------------------------
          \* (B) Properties of the auxiliary sequence ss.
          \*-----------------------------------------------------------
          <5>B0. ss = SelectSeq(external,
                                LAMBDA p : p < hi /\ p > low)
            BY DEF subSeqSmaller
          <5>Bx. external \in Seq(fps) /\ StrAsc(external)
            OBVIOUS
          <5>B1. ss \in Seq(fps)
            BY <5>B0, <5>Bx, SelectSeqInSeqFps
          <5>B2. StrAsc(ss)
            BY <5>B0, <5>Bx, SelectSeqPreservesStrAsc
          <5>B3. low \in Int
            BY <5>A12
          <5>B4. \A i \in 1..Len(ss) :
                   /\ ss[i] > low
                   /\ ss[i] < hi
            BY <5>B0, <5>B3, <5>A17, SelectSeqInWindow
          <5>B5. ss \in Seq(Int)
            BY <5>B1, <5>A11, SeqMonotonic
          <5>B6. newexternal \in Seq(Int)
            BY <5>A11, SeqMonotonic
          \*-----------------------------------------------------------
          \* (C) Concatenation newexternal \o ss is in Seq(fps) and StrAsc.
          \*-----------------------------------------------------------
          <5>C. DEFINE base == newexternal \o ss
          <5>C1. base \in Seq(fps)
            BY <5>B1, ConcatProperties
          <5>C2. base \in Seq(Int)
            BY <5>C1, <5>A11, SeqMonotonic
          <5>C3. StrAsc(base)
            <6>1. CASE newexternal = <<>>
              <7>1. base = <<>> \o ss
                BY <6>1
              <7>2. base = ss
                BY <7>1, <5>B1, ConcatEmptySeq
              <7>. QED  BY <7>2, <5>B2
            <6>2. CASE ss = <<>>
              <7>1. base = newexternal \o <<>>
                BY <6>2
              <7>2. base = newexternal
                BY <7>1, ConcatEmptySeq
              <7>. QED  BY <7>2
            <6>3. CASE newexternal # <<>> /\ ss # <<>>
              <7>1. Len(newexternal) \in Nat  BY LenProperties
              <7>2. Len(newexternal) # 0
                BY <6>3, EmptySeq
              <7>3. Len(newexternal) \in 1..Len(newexternal)
                BY <7>1, <7>2
              <7>4. newexternal[Len(newexternal)] \in fps
                BY <7>3, ElementOfSeq
              <7>5. largestElem(newexternal) =
                      IF newexternal = <<>>
                         THEN 0 ELSE newexternal[Len(newexternal)]
                BY LargestElemDef
              <7>6. low = newexternal[Len(newexternal)]
                BY <7>5, <6>3
              <7>7. Len(ss) \in Nat  BY <5>B1, LenProperties
              <7>8. Len(ss) # 0  BY <5>B1, <6>3, EmptySeq
              <7>9. 1 \in 1..Len(ss)  BY <7>7, <7>8
              <7>10. ss[1] > low
                BY <5>B4, <7>9
              <7>11. newexternal[Len(newexternal)] < ss[1]
                BY <7>6, <7>10, <7>4, <5>A10
              <7>. QED
                BY <5>B2, <5>B5, <5>B6, <7>11, ConcatStrAsc
            <6>. QED  BY <6>1, <6>2, <6>3
          \*-----------------------------------------------------------
          \* (D) Append(base, hi) is in Seq(fps) and StrAsc.
          \*-----------------------------------------------------------
          <5>D1. base = <<>> \/ base[Len(base)] < hi
            <6>1. CASE base = <<>>
              BY <6>1
            <6>2. CASE base # <<>>
              <7>1. Len(base) \in Nat  BY <5>C1, LenProperties
              <7>2. Len(base) # 0  BY <5>C1, <6>2, EmptySeq
              <7>3. Len(base) \in 1..Len(base)
                BY <7>1, <7>2
              <7>. DEFINE n == Len(newexternal)
              <7>. DEFINE m == Len(ss)
              <7>4. Len(base) = n + m
                BY <5>Bx, <5>B1, ConcatProperties
              <7>5. n \in Nat  BY LenProperties
              <7>6. m \in Nat  BY <5>B1, LenProperties
              \* Split on whether ss is empty or not.
              <7>7. CASE ss = <<>>
                <8>1. m = 0  BY <7>7, <5>B1, EmptySeq
                <8>2. base = newexternal \o <<>>
                  BY <7>7
                <8>3. base = newexternal
                  BY <8>2, ConcatEmptySeq
                <8>4. newexternal # <<>>
                  \* If both empty, base = <<>> contradicting <6>2.
                  <9>. SUFFICES ASSUME newexternal = <<>>
                                PROVE  FALSE
                    OBVIOUS
                  <9>1. base = <<>> \o ss  BY @
                  <9>2. base = ss          BY <9>1, ConcatEmptySeq
                  <9>3. base = <<>>        BY <9>2, <7>7
                  <9>. QED  BY <9>3, <6>2
                <8>5. n # 0  BY <8>4, EmptySeq
                <8>6. Len(base) = n
                  BY <8>1, <7>4, <7>5
                <8>7. Len(base) = Len(newexternal)
                  BY <8>6
                <8>8. base[Len(base)] = newexternal[Len(newexternal)]
                  BY <8>3, <8>6
                <8>9. largestElem(newexternal) =
                        IF newexternal = <<>>
                           THEN 0
                           ELSE newexternal[Len(newexternal)]
                  BY LargestElemDef
                <8>10. low = newexternal[Len(newexternal)]
                  BY <8>9, <8>4
                <8>11. hi > newexternal[Len(newexternal)]
                  BY <4>3, <8>10
                <8>. QED  BY <8>8, <8>11
              <7>8. CASE ss # <<>>
                <8>1. m # 0  BY <7>8, <5>B1, EmptySeq
                <8>2. Len(base) = n + m
                  BY <7>4
                <8>3. n + m \in 1..(n + m)
                  BY <8>1, <7>5, <7>6
                <8>4. Len(base) \in Nat /\ Len(base) # 0
                  <9>1. Len(base) \in Nat  BY <7>5, <7>6, <8>2
                  <9>2. Len(base) # 0  BY <8>1, <7>5, <8>2
                  <9>. QED  BY <9>1, <9>2
                \* Element at position Len(base) of newexternal \o ss
                \* equals ss[Len(ss)].
                <8>5. Len(base) - n = m
                  BY <7>5, <7>6, <8>2
                <8>6. Len(base) - n \in 1..m
                  BY <8>5, <8>1, <7>6
                <8>7. base[Len(base)] = ss[Len(base) - n]
                  BY <5>C1, <5>B1, <8>4, <8>6, ConcatProperties
                <8>8. base[Len(base)] = ss[m]
                  BY <8>7, <8>5
                <8>9. m \in 1..m
                  BY <8>1, <7>6
                <8>10. ss[m] < hi
                  BY <5>B4, <8>9
                <8>. QED  BY <8>8, <8>10
              <7>. QED  BY <7>7, <7>8
            <6>. QED  BY <6>1, <6>2
          <5>D2. StrAsc(Append(base, hi))
            BY <5>C2, <5>C3, <5>D1, <5>A17, AppendStrAsc
          <5>D3. Append(base, hi) \in Seq(fps)
            BY <5>C1, <5>A16, AppendProperties
          \*-----------------------------------------------------------
          \* (E) Assemble SortedInv'.
          \*-----------------------------------------------------------
          <5>E1. newexternal' \in Seq(fps)
            BY <5>0, <5>D3
          <5>E2. StrAsc(newexternal')
            BY <5>0, <5>D2
          <5>E3. external' \in Seq(fps)
            BY <5>ext
          <5>E4. StrAsc(external')
            BY <5>ext
          <5>. QED  BY <5>E1, <5>E2, <5>E3, <5>E4
        <4>. QED  BY <4>2, <4>3
      <3>. QED  BY <3>1, <3>2
    <2>. QED  BY <1>3, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Evict
  <1>4. CASE Terminating
    BY <1>4 DEF Terminating, vars
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF Next

(***************************************************************************)
(* SortedInv => Sorted.                                                    *)
(*                                                                         *)
(* `Sorted' is `isSorted(external) /\ isSorted(newexternal)' with          *)
(*                                                                         *)
(*   isSorted(seq) ==                                                      *)
(*     LET sub == SelectSeq(seq, LAMBDA e : e # empty)                     *)
(*     IN  IF Len(sub) < 2 THEN TRUE                                       *)
(*                          ELSE \A i \in 1..(Len(sub)-1): sub[i] < sub[i+1]*)
(*                                                                         *)
(* Since `external, newexternal \in Seq(fps)' and `empty \notin fps' (top  *)
(* level ASSUME), `SelectSeqIdentityOnFps' gives                           *)
(*   sub = SelectSeq(seq, LAMBDA e: e # empty) = seq                       *)
(* and the strict-ascending check reduces to `StrAsc(seq)' which is in     *)
(* `SortedInv'.                                                            *)
(***************************************************************************)
LEMMA SortedInvImpliesSorted == SortedInv => Sorted
  <1>. SUFFICES ASSUME SortedInv  PROVE Sorted
    OBVIOUS
  <1>. USE DEF SortedInv, StrAsc
  <1>1. SelectSeq(external, LAMBDA e : e # empty) = external
    BY SelectSeqIdentityOnFps
  <1>2. SelectSeq(newexternal, LAMBDA e : e # empty) = newexternal
    BY SelectSeqIdentityOnFps
  <1>3. isSorted(external)
    BY <1>1 DEF isSorted
  <1>4. isSorted(newexternal)
    BY <1>2 DEF isSorted
  <1>. QED  BY <1>3, <1>4 DEF Sorted

(***************************************************************************)
(* Main theorem: Spec => []Sorted.                                         *)
(***************************************************************************)
THEOREM SortedSafety == Spec => []Sorted
  \* `SortedInvNext' now requires `EiType /\ DupInv' as additional
  \* hypotheses (to derive `lo'[self] \in fps' in the flush inner-then
  \* case via `TableType').  We therefore thread the full layer-cake
  \* alongside `SortedInv'.  This makes `SortedSafety' transitively
  \* depend on the remaining OMITTEDs in `DupInvNext' (nestedIns, set,
  \* flush outer-else, cas successful), but that dependency is no worse
  \* than the OMITTED that previously lived directly in `SortedInvNext'.
  <1>1. Spec => [](Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                   /\ LoType /\ EvictExclusive /\ DupInv /\ SortedInv)
    <2>1. Init => Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                    /\ LoType /\ EvictExclusive /\ DupInv /\ SortedInv
      BY InitInv, InitStackOK, InitResultType, InitEiType, InitEjType,
         InitLoType, InitEvictExclusive, InitDupInv, InitSortedInv
    <2>2. (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
             /\ LoType /\ EvictExclusive /\ DupInv /\ SortedInv)
            /\ [Next]_vars
          => (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                /\ LoType /\ EvictExclusive /\ DupInv /\ SortedInv)'
      <3>1. Inv /\ StackOK /\ [Next]_vars => Inv'
        BY InvNext
      <3>2. Inv /\ StackOK /\ [Next]_vars => StackOK'
        BY StackOKInd
      <3>3. ResultType /\ [Next]_vars => ResultType'
        BY ResultTypeInd
      <3>4. StackOK /\ EiType /\ [Next]_vars => EiType'
        BY EiTypeInd
      <3>5. StackOK /\ EiType /\ EjType /\ [Next]_vars => EjType'
        BY EjTypeInd
      <3>6. Inv /\ StackOK /\ EiType /\ DupInv /\ LoType /\ [Next]_vars
              => LoType'
        BY LoTypeInd
      <3>7. Inv /\ StackOK /\ EvictExclusive /\ [Next]_vars => EvictExclusive'
        BY EvictExclusiveInd
      <3>8. Inv /\ ResultType /\ EiType /\ EjType /\ LoType
              /\ EvictExclusive /\ DupInv /\ [Next]_vars => DupInv'
        BY DupInvNext
      <3>9. EiType /\ DupInv /\ SortedInv /\ [Next]_vars => SortedInv'
        BY SortedInvNext
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
    <2>. QED  BY <2>1, <2>2, PTL DEF Spec
  <1>2. SortedInv => Sorted
    BY SortedInvImpliesSorted
  <1>. QED  BY <1>1, <1>2, PTL

(***************************************************************************)
(* Membership consistency: every observed fp is either in the table at     *)
(* one of its alternate positions or has been flushed to external.         *)
(*                                                                         *)
(* Required strengthening: Inv \cup Sorted \cup Duplicates \cup            *)
(*   "fp \in history => either it is at idx(fp,k) for some 0<=k<=L         *)
(*    or it is in external".  This is the central correctness invariant    *)
(* of the data structure and the deepest of the OMITTED proofs.            *)
(***************************************************************************)
THEOREM ConsistentSafety == Spec => []Consistent
OMITTED

(***************************************************************************)
(* The full Contains predicate also requires the strengthening above plus  *)
(* a non-membership invariant for fps \ history.                           *)
(***************************************************************************)
THEOREM ContainsSafety == Spec => []Contains
OMITTED

=============================================================================
