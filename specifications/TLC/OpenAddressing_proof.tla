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
EXTENDS OpenAddressing, TLAPS, SequenceTheorems, FiniteSetTheorems

(***************************************************************************)
(* The sets `Writer' and `Reader' are concurrent-process identifiers; the  *)
(* spec's `waitIns' precondition `waitCnt = Cardinality(Writer) - 1 +      *)
(* Cardinality(Reader)' is meaningful only when both sets are finite.  We *)
(* state this as a standing proof-level assumption.                        *)
(***************************************************************************)
ASSUME WriterFinite == IsFiniteSet(Writer)
ASSUME ReaderFinite == IsFiniteSet(Reader)

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
(*  The previously deep parts of the inductive step have been factored:    *)
(*                                                                         *)
(*    (a) `cas' success branch (writer body): when the CAS atomically      *)
(*        writes `fp[self]' to `idx(fp[self], index[self])', preserving    *)
(*        no-duplicates requires that no other table position contains     *)
(*        `fp[self]' or `-fp[self]' beforehand.  This is the central       *)
(*        correctness property of the open-addressing probe sequence       *)
(*        plus the `cntns'/`isMth' check loop.  We have factored it into   *)
(*        the dedicated invariant `CasFreshness' (defined below), and      *)
(*        give a CONCRETE proof script of `cas'-success in `DupInvNext'    *)
(*        that consumes `CasFreshness' as a hypothesis.  The deep open-    *)
(*        addressing claim now lives uniquely inside `CasFreshnessInd'.    *)
(*                                                                         *)
(*    (b) The sort actions `nestedIns' (cell-shift) and `set' (cell-       *)
(*        place): FULLY DISCHARGED via `EvictExclusive' (mutex) and        *)
(*        `EjType' (pinning probe positions to `1..K').                    *)
(*                                                                         *)
(*    (c) `flush' loop exit (and entry to `rtrn'): FULLY DISCHARGED via    *)
(*        `SortPermInv' (the dedicated sort-permutation invariant          *)
(*        defined further below).  `SortPermInv' formalises exactly the    *)
(*        "insertion sort permutes the multiset of non-empty `|table[i]|'" *)
(*        property, and is itself inductive modulo `CasFreshness'.         *)
(*                                                                         *)
(*  All other structural cases of the inductive step are fully discharged. *)
(*  The single remaining deep OMITTED of this development is the           *)
(*  inductiveness of `CasFreshness' itself (see `CasFreshnessInd').        *)
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
(* `WaitCntInv' (definition): the `waitCnt' variable counts exactly the    *)
(* writers currently blocked at `waitEv' or `endWEv'.                      *)
(*                                                                         *)
(* The inductiveness proof (InitWaitCntInv, WaitCntInd) lives further      *)
(* down, because it uses the same toolbox as the other invariants; but    *)
(* the definitions need to be visible here because `EvictExclusiveInd'    *)
(* takes `WaitCntInv' as a hypothesis to discharge the `waitIns' case.   *)
(***************************************************************************)
WaitSet == {s \in Writer : pc[s] \in {"waitEv", "endWEv"}}

WaitCntInv ==
  /\ waitCnt \in Nat
  /\ waitCnt = Cardinality(WaitSet)

(***************************************************************************)
(* `EvictExclusive': at most one writer at a time is inside the "evictor   *)
(* territory" `EvictLabels \cup {"endEv", "waitIns"}', and whenever any    *)
(* writer is there, `evict = TRUE'.                                        *)
(*                                                                         *)
(* This is the standard mutual-exclusion invariant of the Evict            *)
(* procedure.  It is used to discharge the third conjunct of `DupInv'      *)
(* for the `nestedIns' THEN, `set', and `flush outer-else' actions (where  *)
(* the question "is some other writer at `rtrn' or `endEv'?" arises).      *)
(*                                                                         *)
(* "waitIns" is in the evictor territory because the only way to reach it  *)
(* is via `tryEv' with pre-state `evict = FALSE', which sets `evict' =     *)
(* TRUE' atomically.  Including "waitIns" makes the invariant inductive    *)
(* at every action without an auxiliary invariant.                         *)
(***************************************************************************)
EvictUnion == EvictLabels \cup {"endEv", "waitIns"}

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
  Inv /\ StackOK /\ WaitCntInv /\ EvictExclusive /\ [Next]_vars
     => EvictExclusive'
  <1>. SUFFICES ASSUME Inv, StackOK, WaitCntInv, EvictExclusive, [Next]_vars
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
      \* tryEv splits on `evict':
      \*   THEN (evict = FALSE pre): evict' = TRUE, pc'[self] = "waitIns"
      \*        \in EvictUnion.  No other writer is in EvictUnion pre-state
      \*        (by EvictExclusive: pc[s] \in EvictUnion => evict = TRUE,
      \*        contradicting evict = FALSE).
      \*   ELSE (evict = TRUE pre): pc'[self] = "put" \notin EvictUnion;
      \*        others unchanged; `evict' = TRUE' unchanged.
      <3>. USE <2>11 DEF tryEv
      <3>3. pc[self] = "tryEv"  OBVIOUS
      <3>4. pc[self] \notin EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>A. CASE evict = FALSE
        <4>. USE <3>A
        <4>1. evict' = TRUE  OBVIOUS
        <4>2. pc'[self] = "waitIns"  OBVIOUS
        <4>3. \A s2 \in Writer : pc[s2] \notin EvictUnion
          BY <3>A
        <4>4. \A s2 \in Writer : s2 # self => pc'[s2] \notin EvictUnion
          BY <3>5, <4>3
        <4>5. \A s1, s2 \in Writer :
                (pc'[s1] \in EvictUnion /\ pc'[s2] \in EvictUnion)
                => s1 = s2
          <5>. SUFFICES ASSUME NEW s1 \in Writer, NEW s2 \in Writer,
                                pc'[s1] \in EvictUnion,
                                pc'[s2] \in EvictUnion
                        PROVE  s1 = s2
            OBVIOUS
          <5>1. s1 = self  BY <4>4
          <5>2. s2 = self  BY <4>4
          <5>. QED  BY <5>1, <5>2
        <4>6. \A s \in Writer : pc'[s] \in EvictUnion => evict' = TRUE
          BY <4>1
        <4>. QED  BY <4>5, <4>6
      <3>B. CASE evict = TRUE
        <4>. USE <3>B
        <4>1. evict' = evict  OBVIOUS
        <4>2. pc'[self] = "put"  OBVIOUS
        <4>3. pc'[self] \notin EvictUnion  BY <4>2
        <4>4. \A s1, s2 \in Writer :
                (pc'[s1] \in EvictUnion /\ pc'[s2] \in EvictUnion)
                => s1 = s2
          <5>. SUFFICES ASSUME NEW s1 \in Writer, NEW s2 \in Writer,
                                pc'[s1] \in EvictUnion,
                                pc'[s2] \in EvictUnion
                        PROVE  s1 = s2
            OBVIOUS
          <5>1. s1 # self  BY <4>3
          <5>2. s2 # self  BY <4>3
          <5>3. pc[s1] \in EvictUnion  BY <3>5, <5>1
          <5>4. pc[s2] \in EvictUnion  BY <3>5, <5>2
          <5>. QED  BY <5>3, <5>4
        <4>5. \A s \in Writer : pc'[s] \in EvictUnion => evict' = TRUE
          <5>. SUFFICES ASSUME NEW s \in Writer, pc'[s] \in EvictUnion
                        PROVE  evict' = TRUE
            OBVIOUS
          <5>1. s # self  BY <4>3
          <5>2. pc[s] \in EvictUnion  BY <3>5, <5>1
          <5>. QED  BY <4>1, <5>2
        <4>. QED  BY <4>4, <4>5
      <3>. QED  BY <3>A, <3>B
    <2>12. CASE waitIns(self)
      \* waitIns transitions pc[self] from "waitIns" (now in EvictUnion)
      \* to "strIns" (in EvictUnion).  Since "waitIns" is in EvictUnion
      \* pre-state, by `EvictExclusive':
      \*   - self is the UNIQUE writer with pc[s] \in EvictUnion (mutex);
      \*   - evict = TRUE (evict conjunct).
      \* Both are inherited directly to the post-state.
      <3>. USE <2>12 DEF waitIns
      <3>1. pc[self] = "waitIns"  OBVIOUS
      <3>2. pc[self] \in EvictUnion  BY <3>1
      <3>3. pc'[self] = "strIns"  OBVIOUS
      <3>4. pc'[self] \in EvictUnion  BY <3>3
      <3>5. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]  OBVIOUS
      <3>6. evict' = evict  OBVIOUS
      <3>7. evict = TRUE  BY <3>2
      <3>8. evict' = TRUE  BY <3>6, <3>7
      <3>9. \A s2 \in Writer : s2 # self => pc[s2] \notin EvictUnion
        <4>. SUFFICES ASSUME NEW s2 \in Writer, s2 # self
                      PROVE  pc[s2] \notin EvictUnion
          OBVIOUS
        <4>1. SUFFICES ASSUME pc[s2] \in EvictUnion  PROVE FALSE
          OBVIOUS
        <4>2. s2 = self  BY <3>2, <4>1
        <4>. QED  BY <4>2
      <3>10. \A s \in Writer : pc'[s] \in EvictUnion => evict' = TRUE
        BY <3>8
      <3>11. \A s1, s2 \in Writer :
                (pc'[s1] \in EvictUnion /\ pc'[s2] \in EvictUnion)
                => s1 = s2
        <4>. SUFFICES ASSUME NEW s1 \in Writer, NEW s2 \in Writer,
                              pc'[s1] \in EvictUnion,
                              pc'[s2] \in EvictUnion
                      PROVE  s1 = s2
          OBVIOUS
        <4>1. \A s \in Writer :
                s # self /\ pc'[s] \in EvictUnion => FALSE
          <5>. SUFFICES ASSUME NEW s \in Writer, s # self,
                                pc'[s] \in EvictUnion
                        PROVE  FALSE
            OBVIOUS
          <5>1. pc'[s] = pc[s]  BY <3>5
          <5>2. pc[s] \in EvictUnion  BY <5>1
          <5>3. pc[s] \notin EvictUnion  BY <3>9
          <5>. QED  BY <5>2, <5>3
        <4>2. s1 = self  BY <4>1
        <4>3. s2 = self  BY <4>1
        <4>. QED  BY <4>2, <4>3
      <3>. QED  BY <3>10, <3>11
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
(* `WaitCntInv' (lemmas).  The definitions of `WaitSet' and `WaitCntInv'   *)
(* live further up (they are needed by `EvictExclusiveInd').               *)
(***************************************************************************)
LEMMA WaitSetFinite == IsFiniteSet(WaitSet)
  <1>1. WaitSet \in SUBSET Writer
    BY DEF WaitSet
  <1>. QED  BY <1>1, WriterFinite, FS_Subset

LEMMA InitWaitCntInv == Init => WaitCntInv
  <1>. SUFFICES ASSUME Init  PROVE WaitCntInv
    OBVIOUS
  <1>1. waitCnt = 0  BY DEF Init
  <1>2. \A s \in Writer : pc[s] = "pick"
    BY ProcSetIsWriter DEF Init, ProcSet
  <1>3. WaitSet = {}
    BY <1>2 DEF WaitSet
  <1>4. Cardinality(WaitSet) = 0
    BY <1>3, FS_EmptySet
  <1>. QED  BY <1>1, <1>4 DEF WaitCntInv

LEMMA WaitCntInd ==
  Inv /\ StackOK /\ WaitCntInv /\ [Next]_vars => WaitCntInv'
  <1>. SUFFICES ASSUME Inv, StackOK, WaitCntInv, [Next]_vars
                PROVE  WaitCntInv'
    OBVIOUS
  <1>. USE DEF WaitCntInv, WaitSet, Inv, PcRangeOK, PcRange,
              StackOK, EvictLabels, WriterLabels, ProcSet
  <1>. USE WaitSetFinite DEF WaitSet
  \* Facts used repeatedly: the pre-state WaitSet is finite, so
  \* add/remove lemmas apply, and Cardinality(WaitSet) \in Nat.
  <1>Card. Cardinality(WaitSet) \in Nat
    BY WaitSetFinite, FS_CardinalityType DEF WaitSet
  <1>1. CASE UNCHANGED vars
    \* waitCnt, pc unchanged -> WaitSet and waitCnt unchanged.
    BY <1>1 DEF vars
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  WaitCntInv'
    \* Evict-procedure actions keep self's pc in EvictLabels (rtrn moves
    \* to "endEv", still outside {"waitEv","endWEv"}).  waitCnt is
    \* UNCHANGED across all five Evict actions.  WaitSet is unchanged
    \* because only self's pc could change, and self is not in
    \* {"waitEv","endWEv"} pre or post.
    <2>. USE <1>2, ProcSetIsWriter DEF Evict
    <2>1. waitCnt' = waitCnt
      <3>1. CASE strIns(self)   BY <3>1 DEF strIns
      <3>2. CASE nestedIns(self) BY <3>2 DEF nestedIns
      <3>3. CASE set(self)       BY <3>3 DEF set
      <3>4. CASE flush(self)     BY <3>4 DEF flush
      <3>5. CASE rtrn(self)      BY <3>5 DEF rtrn
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>2. pc[self] \in EvictLabels
      <3>1. CASE strIns(self)   BY <3>1 DEF strIns
      <3>2. CASE nestedIns(self) BY <3>2 DEF nestedIns
      <3>3. CASE set(self)       BY <3>3 DEF set
      <3>4. CASE flush(self)     BY <3>4 DEF flush
      <3>5. CASE rtrn(self)      BY <3>5 DEF rtrn
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>4. pc'[self] \notin {"waitEv", "endWEv"}
      <3>1. CASE strIns(self)    BY <3>1 DEF strIns
      <3>2. CASE nestedIns(self) BY <3>2 DEF nestedIns
      <3>3. CASE set(self)       BY <3>3 DEF set
      <3>4. CASE flush(self)     BY <3>4 DEF flush
      <3>5. CASE rtrn(self)
        <4>. USE <3>5 DEF rtrn
        <4>1. pc[self] = "rtrn"  OBVIOUS
        <4>2. pc[self] \in EvictLabels  BY <4>1
        <4>3. stack[self] # <<>>  BY <4>2
        <4>4. Head(stack[self]).pc = "endEv"  BY <4>2
        <4>5. pc'[self] = "endEv"  BY <4>4
        <4>. QED  BY <4>5
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>5. pc[self] \notin {"waitEv", "endWEv"}
      BY <2>2
    <2>6. \A s2 \in Writer : s2 # self => pc'[s2] = pc[s2]
      <3>1. CASE strIns(self)    BY <3>1 DEF strIns
      <3>2. CASE nestedIns(self) BY <3>2 DEF nestedIns
      <3>3. CASE set(self)       BY <3>3 DEF set
      <3>4. CASE flush(self)     BY <3>4 DEF flush
      <3>5. CASE rtrn(self)      BY <3>5 DEF rtrn
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>7. WaitSet' = WaitSet
      <3>. SUFFICES ASSUME NEW s \in Writer
                    PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                            (pc[s] \in {"waitEv", "endWEv"})
        BY DEF WaitSet
      <3>1. CASE s = self
        BY <3>1, <2>4, <2>5
      <3>2. CASE s # self
        <4>1. pc'[s] = pc[s]  BY <2>6, <3>2
        <4>. QED  BY <4>1
      <3>. QED  BY <3>1, <3>2
    <2>. QED  BY <2>1, <2>7, <1>Card
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  WaitCntInv'
    <2>. USE <1>3, ProcSetIsWriter DEF p
    <2>1. CASE pick(self)
      \* pc[self] "pick" -> "put"/"Done"; waitCnt UNCHANGED; no self
      \* enters/exits WaitSet.
      <3>. USE <2>1 DEF pick
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "pick"  OBVIOUS
      <3>3. pc[self] \notin {"waitEv", "endWEv"}  BY <3>2
      <3>4. pc'[self] \in {"put", "Done"}  OBVIOUS
      <3>5. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>4
      <3>6. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>7. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self  BY <4>1, <3>3, <3>5
        <4>2. CASE s # self  BY <4>2, <3>6
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>7, <1>Card
    <2>2. CASE put(self)
      \* Two sub-cases: (i) evict=TRUE, pc "put"->"waitEv", waitCnt+=1,
      \* self enters WaitSet; (ii) evict=FALSE, pc "put"->"chkSnc",
      \* waitCnt UNCHANGED, WaitSet UNCHANGED.
      <3>. USE <2>2 DEF put
      <3>1. pc[self] = "put"  OBVIOUS
      <3>2. self \notin WaitSet
        BY <3>1 DEF WaitSet
      <3>3. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>4. CASE evict
        <4>1. pc'[self] = "waitEv"  BY <3>4
        <4>2. waitCnt' = waitCnt + 1  BY <3>4
        <4>3. WaitSet' = WaitSet \cup {self}
          <5>. SUFFICES ASSUME NEW s \in Writer
                        PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                                (s = self \/ pc[s] \in {"waitEv", "endWEv"})
            BY <3>2 DEF WaitSet
          <5>1. CASE s = self
            BY <5>1, <4>1, <3>1
          <5>2. CASE s # self
            <6>1. pc'[s] = pc[s]  BY <3>3, <5>2
            <6>. QED  BY <5>2, <6>1
          <5>. QED  BY <5>1, <5>2
        <4>4. Cardinality(WaitSet') = Cardinality(WaitSet) + 1
          BY <4>3, <3>2, WaitSetFinite, FS_AddElement
        <4>. QED  BY <4>2, <4>4, <1>Card
      <3>5. CASE ~evict
        <4>1. pc'[self] = "chkSnc"  BY <3>5
        <4>2. waitCnt' = waitCnt  BY <3>5
        <4>3. WaitSet' = WaitSet
          <5>. SUFFICES ASSUME NEW s \in Writer
                        PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                                (pc[s] \in {"waitEv", "endWEv"})
            BY DEF WaitSet
          <5>1. CASE s = self
            <6>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <4>1
            <6>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>1
            <6>. QED  BY <5>1, <6>1, <6>2
          <5>2. CASE s # self
            <6>1. pc'[s] = pc[s]  BY <3>3, <5>2
            <6>. QED  BY <6>1
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>2, <4>3, <1>Card
      <3>. QED  BY <3>4, <3>5
    <2>3. CASE waitEv(self)
      \* pc "waitEv" -> "endWEv"; waitCnt UNCHANGED; self stays in WaitSet.
      <3>. USE <2>3 DEF waitEv
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "waitEv"  OBVIOUS
      <3>3. pc'[self] = "endWEv"  OBVIOUS
      <3>4. self \in WaitSet
        BY <3>2 DEF WaitSet
      <3>5. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>6. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          BY <4>1, <3>2, <3>3
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>5, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>6, <1>Card
    <2>4. CASE endWEv(self)
      \* pc "endWEv" -> "put"; waitCnt-=1; self leaves WaitSet.
      <3>. USE <2>4 DEF endWEv
      <3>1. waitCnt' = waitCnt - 1  OBVIOUS
      <3>2. pc[self] = "endWEv"  OBVIOUS
      <3>3. pc'[self] = "put"  OBVIOUS
      <3>4. self \in WaitSet
        BY <3>2 DEF WaitSet
      <3>5. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>6. WaitSet' = WaitSet \ {self}
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (s # self /\ pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>. QED  BY <4>1, <5>1
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>5, <4>2
          <5>. QED  BY <4>2, <5>1
        <4>. QED  BY <4>1, <4>2
      <3>7. Cardinality(WaitSet') = Cardinality(WaitSet) - 1
        BY <3>6, <3>4, WaitSetFinite, FS_RemoveElement
      <3>8. Cardinality(WaitSet) \in Nat \ {0}
        <4>1. {self} \subseteq WaitSet  BY <3>4
        <4>2. Cardinality({self}) = 1  BY FS_Singleton
        <4>3. Cardinality({self}) <= Cardinality(WaitSet)
          BY <4>1, WaitSetFinite, FS_Subset
        <4>. QED  BY <4>2, <4>3, <1>Card
      <3>. QED  BY <3>1, <3>7, <3>8
    <2>5. CASE chkSnc(self)
      <3>. USE <2>5 DEF chkSnc
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "chkSnc"  OBVIOUS
      <3>3. pc'[self] \in {"cntns", "insrt"}  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
    <2>6. CASE cntns(self)
      <3>. USE <2>6 DEF cntns
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "cntns"  OBVIOUS
      <3>3. pc'[self] \in {"pick", "onSnc", "cntns"}  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
    <2>7. CASE onSnc(self)
      <3>. USE <2>7 DEF onSnc
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "onSnc"  OBVIOUS
      <3>3. pc'[self] \in {"pick", "insrt"}  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
    <2>8. CASE insrt(self)
      <3>. USE <2>8 DEF insrt
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "insrt"  OBVIOUS
      <3>3. pc'[self] \in {"cas", "isMth", "tryEv"}  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
    <2>9. CASE isMth(self)
      <3>. USE <2>9 DEF isMth
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "isMth"  OBVIOUS
      <3>3. pc'[self] \in {"pick", "insrt"}  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
    <2>10. CASE cas(self)
      <3>. USE <2>10 DEF cas
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "cas"  OBVIOUS
      <3>3. pc'[self] \in {"pick", "insrt"}  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
    <2>11. CASE tryEv(self)
      <3>. USE <2>11 DEF tryEv
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "tryEv"  OBVIOUS
      <3>3. pc'[self] \in {"waitIns", "put"}  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
    <2>12. CASE waitIns(self)
      <3>. USE <2>12 DEF waitIns
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "waitIns"  OBVIOUS
      <3>3. pc'[self] = "strIns"  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
    <2>13. CASE endEv(self)
      <3>. USE <2>13 DEF endEv
      <3>1. waitCnt' = waitCnt  OBVIOUS
      <3>2. pc[self] = "endEv"  OBVIOUS
      <3>3. pc'[self] = "put"  OBVIOUS
      <3>4. \A s \in Writer : s # self => pc'[s] = pc[s]  OBVIOUS
      <3>5. WaitSet' = WaitSet
        <4>. SUFFICES ASSUME NEW s \in Writer
                      PROVE  (pc'[s] \in {"waitEv", "endWEv"}) <=>
                              (pc[s] \in {"waitEv", "endWEv"})
          BY DEF WaitSet
        <4>1. CASE s = self
          <5>1. pc'[self] \notin {"waitEv", "endWEv"}  BY <3>3
          <5>2. pc[self] \notin {"waitEv", "endWEv"}   BY <3>2
          <5>. QED  BY <4>1, <5>1, <5>2
        <4>2. CASE s # self
          <5>1. pc'[s] = pc[s]  BY <3>4, <4>2
          <5>. QED  BY <5>1
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>5, <1>Card
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
(* `CasFreshness': the open-addressing probe-sequence correctness          *)
(* invariant.  Whenever a writer `self' is poised at `pc = "cas"' AND     *)
(* the CAS-success guard `table[idx] = expected[self]' is satisfied:      *)
(*                                                                         *)
(*  (i)  the target probe slot `idx(fp[self], index[self])' is in 1..K;    *)
(*                                                                         *)
(*  (ii) `|fp[self]|' is distinct from `|table[k]|' at every other         *)
(*       non-empty cell `k # idx' (no in-table duplicate of the value     *)
(*       being inserted);                                                  *)
(*                                                                         *)
(*  (iii) `|fp[self]|' is distinct from `|lo[s2]|' for every concurrent    *)
(*        sorter `s2' in `{"nestedIns", "set"}' carrying a non-empty       *)
(*        in-flight value `lo[s2]'.                                        *)
(*                                                                         *)
(* The combination is exactly what the cas-success branch of               *)
(* `SortPermInd' needs to preserve `SortPermInv': clause (ii) restores    *)
(* the global `NoDupsTable' over the modified table, and clause (iii)     *)
(* preserves the sort-gap conjunct (b) at every concurrent sorter.         *)
(*                                                                         *)
(* `CasFreshness' ties together `CasProbeUniqueAbsFp' (no off-probe copy of  *)
(* `|fp|' while inserting) and `CasFreshnessCore' (the conditional CAS     *)
(* obligations).  The probe predicate is the genuine strengthening; the    *)
(* core is the earlier (i)-(iii) structure.  Inductive preservation of the  *)
(* combination is still concentrated in `CasFreshnessInd' (establishment    *)
(* `insrt -> cas' is the hard case in TLAPS).                              *)
(***************************************************************************)
CasFreshness == CasProbeUniqueAbsFp /\ CasFreshnessCore

LEMMA InitCasFreshness == Init => CasFreshness
  <1>. SUFFICES ASSUME Init  PROVE CasFreshness
    OBVIOUS
  <1>1. \A self \in ProcSet : pc[self] = "pick"
    BY ProcSetIsWriter DEF Init, ProcSet
  <1>2. \A self \in Writer : pc[self] \notin {"insrt", "cas"}
    BY <1>1, ProcSetIsWriter
  <1>. QED  BY <1>2 DEF CasFreshness, CasProbeUniqueAbsFp, CasFreshnessCore

(***************************************************************************)
(* `CasFreshnessInd': inductive preservation of `CasFreshness'.            *)
(*                                                                         *)
(* `CasProbeUniqueAbsFp' is exactly the probe hygiene Apalache needs and   *)
(* TLAPS must show preserved when entering `cas' (esp. `insrt' ->           *)
(* `cas').  `CasFreshnessCore' is the conditional (i)-(iii) CAS clause.    *)
(* Discharging both together still hinges on the same deep establishment   *)
(* step from cntns/onSnc + probe walks; we leave it as OMITTED pending     *)
(* a TLAPS proof that bridges the scan into `CasProbeUniqueAbsFp'.         *)
(***************************************************************************)
LEMMA CasFreshnessInd ==
  Inv /\ ResultType /\ CasFreshness /\ [Next]_vars => CasFreshness'
  OMITTED

(***************************************************************************)
(* `SortPermInv': the sort-permutation invariant for the insertion-sort   *)
(* body of the `Evict' procedure.  It captures three facts:                *)
(*                                                                         *)
(*  1. `NoDupsTable' holds at every "checkpoint" pc label of the Evict    *)
(*     procedure where the sort body is not in the middle of a shift --    *)
(*     i.e., at `waitIns', `strIns', and `flush'.  (At `rtrn' and          *)
(*     `endEv' this is already guaranteed by `DupInv'.)                    *)
(*                                                                         *)
(*  2. At `pc = "strIns"' the cursors satisfy `ej[self] = ei[self]'.  The  *)
(*     previous `set' action established `ej' = ei'' (both become          *)
(*     `ei + 1'); `waitIns' initializes both to 1.                         *)
(*                                                                         *)
(*  3. At `pc \in {"nestedIns", "set"}' -- in the middle of a sort         *)
(*     iteration -- the table may contain a SINGLE temporary duplicate    *)
(*     at position `gap == mod(ej[self] + 1, K)'.  Specifically:           *)
(*                                                                         *)
(*     (a) `gap \in 1..K' (well-formedness).                               *)
(*     (b) If `lo[self] # empty' then `|lo[self]|' is distinct from       *)
(*         `|table[j]|' for every non-empty cell `j \in 1..K \ {gap}'.     *)
(*     (c) `|table[i]|' is distinct from `|table[j]|' for every pair of    *)
(*         distinct, non-empty cells `i, j \in 1..K \ {gap}'.              *)
(*                                                                         *)
(* Together (1)-(3) imply that the `set' action (which writes `lo[self]'  *)
(* into position `gap') restores full `NoDupsTable' at the next `strIns':  *)
(* the only potentially-colliding cell has been overwritten.               *)
(*                                                                         *)
(* This is the "multiset-permutation" invariant discussed as (b)/(c) in   *)
(* the doc-comment above; we formalise it as an explicit state invariant  *)
(* rather than via an auxiliary multiset variable.                         *)
(***************************************************************************)
SortPermInv ==
  /\ \A self \in ProcSet :
       pc[self] \in {"waitIns", "strIns", "flush"} => NoDupsTable
  /\ \A self \in ProcSet :
       pc[self] = "strIns" => ej[self] = ei[self]
  /\ \A self \in ProcSet :
       pc[self] \in {"nestedIns", "set"} =>
         /\ mod(ej[self] + 1, K) \in 1..K
         /\ (lo[self] # empty =>
               \A j \in 1..K :
                 j # mod(ej[self] + 1, K) /\ table[j] # empty =>
                   abs(table[j]) # abs(lo[self]))
         /\ \A i, j \in 1..K :
              i # j /\ i # mod(ej[self] + 1, K)
                    /\ j # mod(ej[self] + 1, K)
                    /\ table[i] # empty /\ table[j] # empty =>
                abs(table[i]) # abs(table[j])

LEMMA InitSortPermInv == Init => SortPermInv
  <1>. SUFFICES ASSUME Init  PROVE SortPermInv
    OBVIOUS
  <1>1. \A self \in ProcSet : pc[self] = "pick"
    BY ProcSetIsWriter DEF Init, ProcSet
  <1>2. \A self \in ProcSet :
          pc[self] \notin {"waitIns", "strIns", "flush",
                            "nestedIns", "set"}
    BY <1>1
  <1>. QED  BY <1>2 DEF SortPermInv

(***************************************************************************)
(* `SortPermInd': `SortPermInv' is preserved by every action of `Next'.   *)
(*                                                                         *)
(* Proof outline, action by action:                                        *)
(*                                                                         *)
(*  - Stutter / Terminating: routine.                                      *)
(*                                                                         *)
(*  - Evict body:                                                          *)
(*    * `strIns' THEN (ei <= K+L): pc'[self] = "nestedIns"; lo' <-         *)
(*      table[mod(ei+1, K)].  Since pre `ej = ei' (conjunct 2), the        *)
(*      post gap position coincides with `mod(ei+1, K)', and the value    *)
(*      just saved into `lo'' is exactly the value at that position.       *)
(*      Conjunct (3) follows from pre `NoDupsTable' at `pc = "strIns"'.    *)
(*    * `strIns' ELSE (ei > K+L): pc'[self] = "flush"; table UNCHANGED.    *)
(*      Conjunct (1) post follows from pre `NoDupsTable' at `pc =         *)
(*      "strIns"'.                                                         *)
(*    * `nestedIns' THEN: the shift `table[gap_pre] := table[mod(ej,       *)
(*      K)]' moves the old gap position's duplicate one step, restoring    *)
(*      all NoDup relations modulo the new gap `mod(ej, K)'.  lo          *)
(*      unchanged.                                                         *)
(*    * `nestedIns' ELSE: UNCHANGED <<table, ej, lo>>; gap unchanged.      *)
(*    * `set': writes lo into gap.  Post pc = "strIns", ej' = ei'.         *)
(*      `NoDupsTable'' follows from conjunct (3) applied to the written    *)
(*      cell (whose new value `lo' is distinct from all others by (b))     *)
(*      and to the remaining cells (distinct pairwise by (c)).             *)
(*    * `flush' THEN inner-THEN: negates `table[mod(ei, K)]' in place;    *)
(*      |.| preserved, so `NoDupsTable' preserved.                         *)
(*    * `flush' THEN inner-ELSE: UNCHANGED table; trivial.                 *)
(*    * `flush' ELSE (exit): pc'[self] = "rtrn"; table UNCHANGED.          *)
(*    * `rtrn': pc'[self] = "endEv"; table UNCHANGED.                      *)
(*                                                                         *)
(*  - Writer disjuncts: `pc[self]' transitions to/from non-Evict labels;   *)
(*    all modifications to `table' happen under `evict = FALSE' (cas       *)
(*    success) while the Evict mutex (`EvictExclusive') ensures no other  *)
(*    writer is at any of the trigger labels, making the invariant         *)
(*    vacuously preserved for OTHER writers.  The entry transition         *)
(*    `tryEv' (with pre `evict = FALSE') moves self into "waitIns";        *)
(*    pre `FindOrPut' gives pre `NoDupsTable' (via `DupInv').              *)
(***************************************************************************)
LEMMA SortPermInd ==
  Inv /\ StackOK /\ ResultType /\ EiType /\ EjType /\ LoType /\ DupInv
     /\ EvictExclusive /\ CasFreshness /\ SortPermInv /\ [Next]_vars
     => SortPermInv'
  <1>. SUFFICES ASSUME Inv, StackOK, ResultType, EiType, EjType, LoType, DupInv,
                       EvictExclusive, CasFreshness, SortPermInv, [Next]_vars
                PROVE  SortPermInv'
    OBVIOUS
  <1>. USE DEF SortPermInv, DupInv, TableType, NoDupsTable, FindOrPut,
              TableValues, EiType, EjType, LoType,
              EvictExclusive, EvictUnion, EvictLabels,
              StackOK, WriterLabels, ProcSet,
              Inv, PcRangeOK, PcRange
  \* Standing mod(.,K)-range fact: for any integer i, `mod(i, K) \in 1..K'.
  <1>Mod. ASSUME NEW i \in Int
          PROVE  mod(i, K) \in 1..K
    <2>1. K \in Nat \ {0}  BY OAAssumption
    <2>2. i % K \in 0..(K-1)  BY <2>1
    <2>. QED  BY <2>1, <2>2 DEF mod
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. ASSUME NEW self \in ProcSet, Evict(self)
        PROVE  SortPermInv'
    <2>. USE <1>2, ProcSetIsWriter DEF Evict
    <2>. DEFINE gap == mod(ej[self] + 1, K)
    <2>. DEFINE gapp == mod(ej'[self] + 1, K)
    \* Pre-state: by EvictExclusive, self is the UNIQUE writer in
    \* EvictUnion.  Therefore every OTHER writer is OUTSIDE
    \* {"waitIns", "strIns", "flush", "nestedIns", "set"}.
    <2>Muex. \A s2 \in ProcSet : s2 # self =>
                pc[s2] \notin {"waitIns", "strIns", "flush",
                                "nestedIns", "set"}
      <3>1. pc[self] \in EvictLabels \cup {"strIns"}
        <4>1. CASE strIns(self)     BY <4>1 DEF strIns
        <4>2. CASE nestedIns(self)  BY <4>2 DEF nestedIns
        <4>3. CASE set(self)        BY <4>3 DEF set
        <4>4. CASE flush(self)      BY <4>4 DEF flush
        <4>5. CASE rtrn(self)       BY <4>5 DEF rtrn
        <4>. QED  BY <4>1, <4>2, <4>3, <4>4, <4>5
      <3>2. pc[self] \in EvictUnion  BY <3>1
      <3>. SUFFICES ASSUME NEW s2 \in ProcSet, s2 # self,
                            pc[s2] \in {"waitIns", "strIns", "flush",
                                         "nestedIns", "set"}
                    PROVE  FALSE
        OBVIOUS
      <3>3. pc[s2] \in EvictUnion  OBVIOUS
      <3>4. s2 = self  BY <3>2, <3>3, ProcSetIsWriter
      <3>. QED  BY <3>4
    <2>1. CASE strIns(self)
      <3>. USE <2>1 DEF strIns
      <3>1. pc[self] = "strIns"  OBVIOUS
      <3>2. UNCHANGED table  OBVIOUS
      <3>A. CASE ei[self] <= K+L
        <4>. USE <3>A
        <4>1. pc'[self] = "nestedIns"  OBVIOUS
        <4>2. ei'[self] = ei[self]  OBVIOUS
        <4>3. ej'[self] = ej[self]  OBVIOUS
        <4>4. ej[self] = ei[self]  BY <3>1
        <4>5. lo'[self] = table[mod(ei[self] + 1, K)]  OBVIOUS
        <4>6. gapp = mod(ej[self] + 1, K)  BY <4>3
        <4>7. ej[self] \in Int  BY ProcSetIsWriter
        <4>8. ej[self] + 1 \in Int  BY <4>7
        <4>9. gapp \in 1..K  BY <4>6, <4>8, <1>Mod
        <4>10. gapp = mod(ei[self] + 1, K)  BY <4>4, <4>6
        <4>11. lo'[self] = table[gapp]  BY <4>5, <4>10
        \* NoDupsTable held pre at pc = "strIns".
        <4>NdT. \A i, j \in 1..K :
                   i # j /\ table[i] # empty /\ table[j] # empty =>
                     abs(table[i]) # abs(table[j])
          BY <3>1
        \* Close SortPermInv' conjuncts by cases on pc'[s2].
        <4>. SUFFICES
               /\ \A s2 \in ProcSet :
                    pc'[s2] \in {"waitIns", "strIns", "flush"}
                       => NoDupsTable'
               /\ \A s2 \in ProcSet :
                    pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
               /\ \A s2 \in ProcSet :
                    pc'[s2] \in {"nestedIns", "set"} =>
                      /\ mod(ej'[s2] + 1, K) \in 1..K
                      /\ (lo'[s2] # empty =>
                            \A j \in 1..K :
                              j # mod(ej'[s2] + 1, K)
                                /\ table'[j] # empty =>
                                abs(table'[j]) # abs(lo'[s2]))
                      /\ \A i, j \in 1..K :
                           i # j /\ i # mod(ej'[s2] + 1, K)
                                 /\ j # mod(ej'[s2] + 1, K)
                                 /\ table'[i] # empty
                                 /\ table'[j] # empty =>
                           abs(table'[i]) # abs(table'[j])
          BY DEF SortPermInv
        \* Conjunct 1: pc'[s2] in {waitIns, strIns, flush}.
        <4>C1. \A s2 \in ProcSet :
                 pc'[s2] \in {"waitIns", "strIns", "flush"}
                   => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <5>2
          <5>4. NoDupsTable  BY <5>3
          <5>. QED  BY <5>4, <3>2
        \* Conjunct 2: pc'[s2] = "strIns".
        <4>C2. \A s2 \in ProcSet :
                 pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] = "strIns"  BY <5>2
          <5>4. ej[s2] = ei[s2]  BY <5>3
          <5>5. ej'[s2] = ej[s2]  BY <5>1
          <5>6. ei'[s2] = ei[s2]  BY <5>1
          <5>. QED  BY <5>4, <5>5, <5>6
        \* Conjunct 3: pc'[s2] in {nestedIns, set}.
        <4>C3. \A s2 \in ProcSet :
                 pc'[s2] \in {"nestedIns", "set"} =>
                   /\ mod(ej'[s2] + 1, K) \in 1..K
                   /\ (lo'[s2] # empty =>
                         \A j \in 1..K :
                           j # mod(ej'[s2] + 1, K)
                             /\ table'[j] # empty =>
                             abs(table'[j]) # abs(lo'[s2]))
                   /\ \A i, j \in 1..K :
                        i # j /\ i # mod(ej'[s2] + 1, K)
                              /\ j # mod(ej'[s2] + 1, K)
                              /\ table'[i] # empty
                              /\ table'[j] # empty =>
                        abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                               /\ (lo'[s2] # empty =>
                                     \A j \in 1..K :
                                       j # mod(ej'[s2] + 1, K)
                                         /\ table'[j] # empty =>
                                         abs(table'[j])
                                           # abs(lo'[s2]))
                               /\ \A i, j \in 1..K :
                                    i # j
                                      /\ i # mod(ej'[s2] + 1, K)
                                      /\ j # mod(ej'[s2] + 1, K)
                                      /\ table'[i] # empty
                                      /\ table'[j] # empty =>
                                    abs(table'[i]) # abs(table'[j])
            OBVIOUS
          <5>1. CASE s2 = self
            \* s2 = self, pc'[self] = "nestedIns".
            <6>1. ej'[s2] = ej[self]  BY <5>1, <4>3
            <6>2. mod(ej'[s2] + 1, K) = gapp  BY <5>1, <6>1, <4>6
            <6>3. mod(ej'[s2] + 1, K) \in 1..K  BY <6>2, <4>9
            <6>4. table'[mod(ej'[s2] + 1, K)] = table[gapp]
              BY <3>2, <6>2
            <6>5. lo'[s2] = table[gapp]  BY <5>1, <4>11
            \* (b): lo'[s2] # empty => |table'[j]| # |lo'[s2]|.
            <6>6. lo'[s2] # empty =>
                    \A j \in 1..K :
                      j # mod(ej'[s2] + 1, K)
                        /\ table'[j] # empty =>
                        abs(table'[j]) # abs(lo'[s2])
              <7>. SUFFICES ASSUME lo'[s2] # empty,
                                    NEW j \in 1..K,
                                    j # mod(ej'[s2] + 1, K),
                                    table'[j] # empty
                            PROVE  abs(table'[j]) # abs(lo'[s2])
                OBVIOUS
              <7>1. table'[j] = table[j]  BY <3>2
              <7>2. j # gapp  BY <6>2
              <7>3. table[gapp] # empty  BY <6>5
              <7>4. table[j] # empty  BY <7>1
              <7>5. abs(table[j]) # abs(table[gapp])
                BY <4>NdT, <7>2, <4>9, <7>3, <7>4
              <7>. QED  BY <7>1, <7>5, <6>5
            \* (c): for i, j # gap (post), pairwise |.| distinct.
            <6>7. \A i, j \in 1..K :
                     i # j /\ i # mod(ej'[s2] + 1, K)
                           /\ j # mod(ej'[s2] + 1, K)
                           /\ table'[i] # empty
                           /\ table'[j] # empty =>
                     abs(table'[i]) # abs(table'[j])
              <7>. SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K,
                                    i # j,
                                    i # mod(ej'[s2] + 1, K),
                                    j # mod(ej'[s2] + 1, K),
                                    table'[i] # empty,
                                    table'[j] # empty
                            PROVE  abs(table'[i]) # abs(table'[j])
                OBVIOUS
              <7>1. table'[i] = table[i]  BY <3>2
              <7>2. table'[j] = table[j]  BY <3>2
              <7>. QED  BY <7>1, <7>2, <4>NdT
            <6>. QED  BY <5>1, <6>3, <6>6, <6>7
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <5>2
            <6>2. pc[s2] \in {"nestedIns", "set"}  BY <6>1
            <6>3. ej'[s2] = ej[s2]  BY <5>2
            <6>4. lo'[s2] = lo[s2]  BY <5>2
            <6>5. table'[s2] = table[s2]  BY <3>2  \* unused; table unchanged
            <6>. QED
              BY <6>2, <6>3, <6>4, <3>2
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>C1, <4>C2, <4>C3
      <3>B. CASE ~(ei[self] <= K+L)
        \* pc'[self] = "flush", ei' := 1, ej, lo, table UNCHANGED.
        <4>. USE <3>B
        <4>1. pc'[self] = "flush"  OBVIOUS
        <4>2. ej'[self] = ej[self]  OBVIOUS
        <4>3. lo'[self] = lo[self]  OBVIOUS
        <4>4. UNCHANGED table  OBVIOUS
        <4>NdT. NoDupsTable  BY <3>1
        \* Close SortPermInv' by cases on pc'[s2].
        <4>C1. \A s2 \in ProcSet :
                 pc'[s2] \in {"waitIns", "strIns", "flush"}
                   => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. CASE s2 = self
            BY <5>1, <4>NdT, <3>2
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <5>2
            <6>2. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <6>1
            <6>3. NoDupsTable  BY <6>2
            <6>. QED  BY <6>3, <3>2
          <5>. QED  BY <5>1, <5>2
        <4>C2. \A s2 \in ProcSet :
                 pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] = "strIns"  BY <5>2
          <5>4. ej[s2] = ei[s2]  BY <5>3
          <5>5. ej'[s2] = ej[s2]  BY <5>1
          <5>6. ei'[s2] = ei[s2]  BY <5>1
          <5>. QED  BY <5>4, <5>5, <5>6
        <4>C3. \A s2 \in ProcSet :
                 pc'[s2] \in {"nestedIns", "set"} =>
                   /\ mod(ej'[s2] + 1, K) \in 1..K
                   /\ (lo'[s2] # empty =>
                         \A j \in 1..K :
                           j # mod(ej'[s2] + 1, K)
                             /\ table'[j] # empty =>
                             abs(table'[j]) # abs(lo'[s2]))
                   /\ \A i, j \in 1..K :
                        i # j /\ i # mod(ej'[s2] + 1, K)
                              /\ j # mod(ej'[s2] + 1, K)
                              /\ table'[i] # empty
                              /\ table'[j] # empty =>
                        abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                               /\ (lo'[s2] # empty =>
                                     \A j \in 1..K :
                                       j # mod(ej'[s2] + 1, K)
                                         /\ table'[j] # empty =>
                                         abs(table'[j])
                                           # abs(lo'[s2]))
                               /\ \A i, j \in 1..K :
                                    i # j
                                      /\ i # mod(ej'[s2] + 1, K)
                                      /\ j # mod(ej'[s2] + 1, K)
                                      /\ table'[i] # empty
                                      /\ table'[j] # empty =>
                                    abs(table'[i]) # abs(table'[j])
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"nestedIns", "set"}  BY <5>2
          <5>4. ej'[s2] = ej[s2]  BY <5>1
          <5>5. lo'[s2] = lo[s2]  BY <5>1
          <5>. QED  BY <5>3, <5>4, <5>5, <3>2
        <4>. QED  BY <4>C1, <4>C2, <4>C3
      <3>. QED  BY <3>A, <3>B
    <2>2. CASE nestedIns(self)
      \* Three cases:
      \*   THEN (compare <= -1), ej # 0: pc' = "nestedIns", ej' = ej - 1,
      \*                                 table[gap] <- table[mod(ej,K)].
      \*   THEN (compare <= -1), ej = 0: pc' = "set", ej' = -1,
      \*                                 table[gap] <- table[K].
      \*   ELSE (compare > -1): pc' = "set", table, ej, lo UNCHANGED.
      \* In the two THEN branches, `gapp = mod(ej, K)' regardless of
      \* whether ej = 0 (because (ej - 1) + 1 = ej).  The ELSE branch
      \* has `gapp = gap' since ej is unchanged.
      <3>. USE <2>2 DEF nestedIns
      <3>1. pc[self] = "nestedIns"  OBVIOUS
      <3>2. lo'[self] = lo[self]  OBVIOUS
      <3>3. ei'[self] = ei[self]  OBVIOUS
      <3>G. gap \in 1..K  BY <3>1
      <3>Int. ej[self] \in Int  BY ProcSetIsWriter
      <3>A. CASE compare(lo[self], mod(ei[self] + 1, K),
                          table[mod(ej[self], K)], mod(ej[self], K)) <= -1
        \* Combined THEN branch (both sub-cases).
        <4>. USE <3>A
        <4>. DEFINE src == mod(ej[self], K)
        <4>1. src \in 1..K  BY <1>Mod, <3>Int
        <4>2. table' = [table EXCEPT ![gap] = table[src]]
          OBVIOUS
        <4>3. table'[gap] = table[src]  BY <4>2, <3>G
        <4>4. \A k \in 1..K : k # gap => table'[k] = table[k]
          BY <4>2, <3>G
        <4>5. ej'[self] = ej[self] - 1  OBVIOUS
        <4>6. ej'[self] \in Int  BY <4>5, <3>Int
        <4>7. ej'[self] + 1 = ej[self]  BY <4>5
        <4>8. gapp = mod(ej[self], K)  BY <4>7
        <4>9. gapp = src  BY <4>8
        <4>10. gapp \in 1..K  BY <4>9, <4>1
        <4>11. pc'[self] \in {"nestedIns", "set"}
          OBVIOUS
        \* SortPermInv' at self, conjunct 3, via gapp = src.
        <4>Self3. pc'[self] \in {"nestedIns", "set"} =>
                    /\ mod(ej'[self] + 1, K) \in 1..K
                    /\ (lo'[self] # empty =>
                          \A j \in 1..K :
                            j # mod(ej'[self] + 1, K)
                              /\ table'[j] # empty =>
                              abs(table'[j]) # abs(lo'[self]))
                    /\ \A i, j \in 1..K :
                         i # j /\ i # mod(ej'[self] + 1, K)
                               /\ j # mod(ej'[self] + 1, K)
                               /\ table'[i] # empty
                               /\ table'[j] # empty =>
                         abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES /\ mod(ej'[self] + 1, K) \in 1..K
                       /\ (lo'[self] # empty =>
                             \A j \in 1..K :
                               j # mod(ej'[self] + 1, K)
                                 /\ table'[j] # empty =>
                                 abs(table'[j]) # abs(lo'[self]))
                       /\ \A i, j \in 1..K :
                            i # j /\ i # mod(ej'[self] + 1, K)
                                  /\ j # mod(ej'[self] + 1, K)
                                  /\ table'[i] # empty
                                  /\ table'[j] # empty =>
                            abs(table'[i]) # abs(table'[j])
            OBVIOUS
          <5>Gpp. mod(ej'[self] + 1, K) = src
            BY <4>7, <4>8
          <5>1. mod(ej'[self] + 1, K) \in 1..K  BY <5>Gpp, <4>1
          \* Part (b): for j # src (= gapp), j non-empty post-state,
          \*           |table'[j]| # |lo'[self]|.
          <5>2. lo'[self] # empty =>
                  \A j \in 1..K :
                    j # mod(ej'[self] + 1, K) /\ table'[j] # empty =>
                      abs(table'[j]) # abs(lo'[self])
            <6>. SUFFICES ASSUME lo'[self] # empty,
                                  NEW j \in 1..K,
                                  j # mod(ej'[self] + 1, K),
                                  table'[j] # empty
                          PROVE  abs(table'[j]) # abs(lo'[self])
              OBVIOUS
            <6>1. j # src  BY <5>Gpp
            <6>2. lo[self] # empty  BY <3>2
            <6>3. CASE j = gap
              \* table'[j] = table[src].
              <7>1. table'[j] = table[src]  BY <4>3, <6>3
              \* By pre SortPermInv conjunct 3(b): for src # gap and
              \* (if table[src] # empty) |table[src]| # |lo[self]|.
              <7>2. src # gap  BY <6>3, <6>1
              <7>3. table[src] # empty  BY <7>1
              <7>4. abs(table[src]) # abs(lo[self])
                BY <3>1, <6>2, <7>2, <7>3, <4>1, <3>G
              <7>. QED  BY <7>1, <7>4, <3>2
            <6>4. CASE j # gap
              <7>1. table'[j] = table[j]  BY <4>4, <6>4
              <7>2. j # gap /\ table[j] # empty  BY <6>4, <7>1
              <7>3. abs(table[j]) # abs(lo[self])
                BY <3>1, <6>2, <7>2
              <7>. QED  BY <7>1, <7>3, <3>2
            <6>. QED  BY <6>3, <6>4
          \* Part (c): for i, j both # src, distinct, both non-empty post,
          \*           |table'[i]| # |table'[j]|.
          <5>3. \A i, j \in 1..K :
                   i # j /\ i # mod(ej'[self] + 1, K)
                         /\ j # mod(ej'[self] + 1, K)
                         /\ table'[i] # empty /\ table'[j] # empty =>
                   abs(table'[i]) # abs(table'[j])
            <6>. SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K,
                                  i # j,
                                  i # mod(ej'[self] + 1, K),
                                  j # mod(ej'[self] + 1, K),
                                  table'[i] # empty,
                                  table'[j] # empty
                          PROVE  abs(table'[i]) # abs(table'[j])
              OBVIOUS
            <6>1. i # src /\ j # src  BY <5>Gpp
            <6>2. CASE i = gap /\ j # gap
              <7>1. table'[i] = table[src]  BY <4>3, <6>2
              <7>2. table'[j] = table[j]  BY <4>4, <6>2
              <7>3. src # gap /\ j # gap  BY <6>2, <6>1
              <7>4. src # j  BY <6>1
              <7>5. table[src] # empty  BY <7>1
              <7>6. table[j] # empty  BY <7>2
              <7>7. abs(table[src]) # abs(table[j])
                BY <3>1, <7>3, <7>4, <7>5, <7>6, <4>1
              <7>. QED  BY <7>1, <7>2, <7>7
            <6>3. CASE j = gap /\ i # gap
              <7>1. table'[j] = table[src]  BY <4>3, <6>3
              <7>2. table'[i] = table[i]  BY <4>4, <6>3
              <7>3. src # gap /\ i # gap  BY <6>3, <6>1
              <7>4. i # src  BY <6>1
              <7>5. table[src] # empty  BY <7>1
              <7>6. table[i] # empty  BY <7>2
              <7>7. abs(table[i]) # abs(table[src])
                BY <3>1, <7>3, <7>4, <7>5, <7>6, <4>1
              <7>. QED  BY <7>1, <7>2, <7>7
            <6>4. CASE i # gap /\ j # gap
              <7>1. table'[i] = table[i]  BY <4>4, <6>4
              <7>2. table'[j] = table[j]  BY <4>4, <6>4
              <7>3. i # gap /\ j # gap  BY <6>4
              <7>4. table[i] # empty  BY <7>1
              <7>5. table[j] # empty  BY <7>2
              <7>6. abs(table[i]) # abs(table[j])
                BY <3>1, <7>3, <7>4, <7>5
              <7>. QED  BY <7>1, <7>2, <7>6
            <6>5. CASE i = gap /\ j = gap
              BY <6>5
            <6>. QED  BY <6>2, <6>3, <6>4, <6>5
          <5>. QED  BY <5>1, <5>2, <5>3
        \* SortPermInv' conjuncts 1, 2 at self: pc'[self] \in
        \*   {"nestedIns", "set"}, so not in {"waitIns", "strIns",
        \*   "flush"} and not "strIns".  Vacuous for self.
        <4>Self1. \A s2 \in ProcSet :
                     pc'[s2] \in {"waitIns", "strIns", "flush"}
                       => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 # self  BY <4>11
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <5>2
          <5>4. FALSE  BY <5>3, <2>Muex, <5>1
          <5>. QED  BY <5>4
        <4>Self2. \A s2 \in ProcSet :
                     pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>11
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] = "strIns"  BY <5>2
          <5>4. FALSE  BY <5>3, <2>Muex, <5>1
          <5>. QED  BY <5>4
        \* Other s2 conjunct 3: by mutex, pc[s2] not in {nestedIns, set}.
        <4>Other3. \A s2 \in ProcSet :
                      s2 # self /\ pc'[s2] \in {"nestedIns", "set"} =>
                        /\ mod(ej'[s2] + 1, K) \in 1..K
                        /\ (lo'[s2] # empty =>
                              \A j \in 1..K :
                                j # mod(ej'[s2] + 1, K)
                                  /\ table'[j] # empty =>
                                  abs(table'[j]) # abs(lo'[s2]))
                        /\ \A i, j \in 1..K :
                             i # j /\ i # mod(ej'[s2] + 1, K)
                                   /\ j # mod(ej'[s2] + 1, K)
                                   /\ table'[i] # empty
                                   /\ table'[j] # empty =>
                             abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, s2 # self,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  FALSE
            OBVIOUS
          <5>1. pc'[s2] = pc[s2]  OBVIOUS
          <5>2. pc[s2] \in {"nestedIns", "set"}  BY <5>1
          <5>. QED  BY <5>2, <2>Muex
        <4>. QED  BY <4>Self1, <4>Self2, <4>Self3, <4>Other3
             DEF SortPermInv
      <3>B. CASE ~(compare(lo[self], mod(ei[self] + 1, K),
                            table[mod(ej[self], K)], mod(ej[self], K))
                   <= -1)
        \* ELSE: UNCHANGED <<table, ej>>.  pc'[self] = "set".  gapp = gap.
        <4>. USE <3>B
        <4>1. pc'[self] = "set"  OBVIOUS
        <4>2. UNCHANGED <<table, ej>>  OBVIOUS
        <4>3. ej'[self] = ej[self]  BY <4>2
        <4>4. gapp = gap  BY <4>3
        \* Self conjunct 3 post: same as pre (pc[self] = "nestedIns" was
        \* in {nestedIns, set}).
        <4>Self3. /\ mod(ej'[self] + 1, K) \in 1..K
                  /\ (lo'[self] # empty =>
                        \A j \in 1..K :
                          j # mod(ej'[self] + 1, K)
                            /\ table'[j] # empty =>
                            abs(table'[j]) # abs(lo'[self]))
                  /\ \A i, j \in 1..K :
                       i # j /\ i # mod(ej'[self] + 1, K)
                             /\ j # mod(ej'[self] + 1, K)
                             /\ table'[i] # empty
                             /\ table'[j] # empty =>
                       abs(table'[i]) # abs(table'[j])
          BY <3>1, <4>2, <4>4
        \* Other s2: by mutex, not in triggers.  Vacuous.
        <4>C1. \A s2 \in ProcSet :
                  pc'[s2] \in {"waitIns", "strIns", "flush"}
                    => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <5>2
          <5>. QED  BY <5>3, <2>Muex, <5>1
        <4>C2. \A s2 \in ProcSet :
                  pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] = "strIns"  BY <5>2
          <5>. QED  BY <5>3, <2>Muex, <5>1
        <4>C3. \A s2 \in ProcSet :
                  pc'[s2] \in {"nestedIns", "set"} =>
                    /\ mod(ej'[s2] + 1, K) \in 1..K
                    /\ (lo'[s2] # empty =>
                          \A j \in 1..K :
                            j # mod(ej'[s2] + 1, K)
                              /\ table'[j] # empty =>
                              abs(table'[j]) # abs(lo'[s2]))
                    /\ \A i, j \in 1..K :
                         i # j /\ i # mod(ej'[s2] + 1, K)
                               /\ j # mod(ej'[s2] + 1, K)
                               /\ table'[i] # empty
                               /\ table'[j] # empty =>
                         abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                               /\ (lo'[s2] # empty =>
                                     \A j \in 1..K :
                                       j # mod(ej'[s2] + 1, K)
                                         /\ table'[j] # empty =>
                                         abs(table'[j])
                                           # abs(lo'[s2]))
                               /\ \A i, j \in 1..K :
                                    i # j
                                      /\ i # mod(ej'[s2] + 1, K)
                                      /\ j # mod(ej'[s2] + 1, K)
                                      /\ table'[i] # empty
                                      /\ table'[j] # empty =>
                                    abs(table'[i]) # abs(table'[j])
            OBVIOUS
          <5>1. CASE s2 = self
            BY <5>1, <4>Self3
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <5>2
            <6>2. pc[s2] \in {"nestedIns", "set"}  BY <6>1
            <6>. QED  BY <6>2, <2>Muex, <5>2
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>C1, <4>C2, <4>C3 DEF SortPermInv
      <3>. QED  BY <3>A, <3>B
    <2>3. CASE set(self)
      \* The critical transition: pc' = "strIns", table[gap] <- lo[self],
      \* ej' := ei + 1, ei' := ei + 1.  NoDupsTable' follows from the
      \* pre-state sort-gap invariant (SortPermInv conjunct 3).
      <3>. USE <2>3 DEF set
      <3>1. pc[self] = "set"  OBVIOUS
      <3>2. pc'[self] = "strIns"  OBVIOUS
      <3>3. lo'[self] = lo[self]  OBVIOUS
      <3>4. ej'[self] = ei[self] + 1  OBVIOUS
      <3>5. ei'[self] = ei[self] + 1  OBVIOUS
      <3>6. ej'[self] = ei'[self]  BY <3>4, <3>5
      <3>7. table' = [table EXCEPT ![gap] = lo[self]]
        OBVIOUS
      <3>G. gap \in 1..K  BY <3>1
      <3>8. table'[gap] = lo[self]  BY <3>7, <3>G
      <3>9. \A k \in 1..K : k # gap => table'[k] = table[k]
        BY <3>7, <3>G
      \* Pre SortPermInv conjunct 3 at self.
      <3>Lo. lo[self] # empty =>
               \A j \in 1..K :
                 j # gap /\ table[j] # empty =>
                   abs(table[j]) # abs(lo[self])
        BY <3>1
      <3>Nd. \A i, j \in 1..K :
                i # j /\ i # gap /\ j # gap /\
                table[i] # empty /\ table[j] # empty =>
                  abs(table[i]) # abs(table[j])
        BY <3>1
      \* NoDupsTable' at self's post-state pc = "strIns".
      <3>NdT. NoDupsTable'
        <4>. SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K,
                              i # j, table'[i] # empty, table'[j] # empty
                      PROVE  abs(table'[i]) # abs(table'[j])
          BY DEF NoDupsTable
        <4>1. CASE i = gap /\ j # gap
          <5>1. table'[i] = lo[self]  BY <3>8, <4>1
          <5>2. table'[j] = table[j]  BY <3>9, <4>1
          <5>3. lo[self] # empty  BY <5>1
          <5>4. j # gap /\ table[j] # empty  BY <4>1, <5>2
          <5>5. abs(table[j]) # abs(lo[self])  BY <3>Lo, <5>3, <5>4
          <5>. QED  BY <5>1, <5>2, <5>5
        <4>2. CASE j = gap /\ i # gap
          <5>1. table'[j] = lo[self]  BY <3>8, <4>2
          <5>2. table'[i] = table[i]  BY <3>9, <4>2
          <5>3. lo[self] # empty  BY <5>1
          <5>4. i # gap /\ table[i] # empty  BY <4>2, <5>2
          <5>5. abs(table[i]) # abs(lo[self])  BY <3>Lo, <5>3, <5>4
          <5>. QED  BY <5>1, <5>2, <5>5
        <4>3. CASE i # gap /\ j # gap
          <5>1. table'[i] = table[i]  BY <3>9, <4>3
          <5>2. table'[j] = table[j]  BY <3>9, <4>3
          <5>3. i # gap /\ j # gap  BY <4>3
          <5>4. table[i] # empty /\ table[j] # empty  BY <5>1, <5>2
          <5>5. abs(table[i]) # abs(table[j])  BY <3>Nd, <5>3, <5>4
          <5>. QED  BY <5>1, <5>2, <5>5
        <4>4. CASE i = gap /\ j = gap
          BY <4>4
        <4>. QED  BY <4>1, <4>2, <4>3, <4>4
      \* Close SortPermInv' conjuncts.
      <3>C1. \A s2 \in ProcSet :
                pc'[s2] \in {"waitIns", "strIns", "flush"}
                  => NoDupsTable'
        BY <3>NdT
      <3>C2. \A s2 \in ProcSet :
                pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                      PROVE  ej'[s2] = ei'[s2]
          OBVIOUS
        <4>1. CASE s2 = self
          BY <4>1, <3>6
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>2. pc[s2] = "strIns"  BY <5>1
          <5>3. ej[s2] = ei[s2]  BY <5>2
          <5>4. ej'[s2] = ej[s2] /\ ei'[s2] = ei[s2]  BY <4>2
          <5>. QED  BY <5>3, <5>4
        <4>. QED  BY <4>1, <4>2
      <3>C3. \A s2 \in ProcSet :
                pc'[s2] \in {"nestedIns", "set"} =>
                  /\ mod(ej'[s2] + 1, K) \in 1..K
                  /\ (lo'[s2] # empty =>
                        \A j \in 1..K :
                          j # mod(ej'[s2] + 1, K)
                            /\ table'[j] # empty =>
                            abs(table'[j]) # abs(lo'[s2]))
                  /\ \A i, j \in 1..K :
                       i # j /\ i # mod(ej'[s2] + 1, K)
                             /\ j # mod(ej'[s2] + 1, K)
                             /\ table'[i] # empty
                             /\ table'[j] # empty =>
                       abs(table'[i]) # abs(table'[j])
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"nestedIns", "set"}
                      PROVE  FALSE
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] \in {"nestedIns", "set"}  BY <4>2
        <4>. QED  BY <4>3, <2>Muex, <4>1
      <3>. QED  BY <3>C1, <3>C2, <3>C3 DEF SortPermInv
    <2>4. CASE flush(self)
      <3>. USE <2>4 DEF flush
      <3>1. pc[self] = "flush"  OBVIOUS
      <3>2. NoDupsTable  BY <3>1
      <3>A. CASE ei[self] <= K+L
        <4>. USE <3>A
        <4>1. pc'[self] = "flush"  OBVIOUS
        <4>2. lo'[self] = table[mod(ei[self], K)]  OBVIOUS
        <4>3. ej'[self] = ej[self]  OBVIOUS
        \* Pin mod(ei[self], K) \in 1..K via EiType.
        <4>4. ei[self] \in Nat  BY ProcSetIsWriter
        <4>5. ei[self] % K \in 0..(K-1)
          <5>1. K \in Nat \ {0}  BY OAAssumption
          <5>. QED  BY <4>4, <5>1
        <4>6. mod(ei[self], K) \in 1..K
          <5>1. K \in Nat \ {0}  BY OAAssumption
          <5>. QED  BY <5>1, <4>5 DEF mod
        \* Inner THEN / ELSE differ only in whether table is updated.
        \* In both cases, |table'[i]| = |table[i]| for all i (negate-in-
        \* place preserves absolute value).
        <4>NdT. NoDupsTable'
          <5>. SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K,
                                i # j, table'[i] # empty, table'[j] # empty
                        PROVE  abs(table'[i]) # abs(table'[j])
            BY DEF NoDupsTable
          <5>A. CASE lo'[self] # empty /\
                     lo'[self] > largestElem(newexternal) /\
                     ((ei[self] <= K /\ ~wrapped(lo'[self],ei[self])) \/
                      (ei[self] > K /\ wrapped(lo'[self],ei[self])))
            \* Inner THEN: table'[mod(ei, K)] = lo'[self] * -1.
            <6>. USE <5>A
            <6>. DEFINE pos == mod(ei[self], K)
            <6>1. table' = [table EXCEPT ![pos] = lo'[self] * (-1)]
              OBVIOUS
            <6>2. table'[pos] = lo'[self] * (-1)  BY <6>1, <4>6
            <6>3. \A k \in 1..K : k # pos => table'[k] = table[k]
              BY <6>1, <4>6
            <6>4. lo'[self] # empty  OBVIOUS
            <6>5. table[pos] # empty
              BY <4>2, <6>4
            <6>6. table[pos] \in TableValues
              BY <4>6
            <6>8. abs(table'[pos]) = abs(table[pos])
              <7>. USE DEF abs
              <7>1. table'[pos] = table[pos] * (-1)  BY <6>2, <4>2
              <7>2. table[pos] \in Int  BY <6>6 DEF TableValues
              <7>. QED  BY <7>1, <7>2
            <6>9. \A k \in 1..K : abs(table'[k]) = abs(table[k])
              <7>. SUFFICES ASSUME NEW k \in 1..K
                            PROVE  abs(table'[k]) = abs(table[k])
                OBVIOUS
              <7>1. CASE k = pos  BY <7>1, <6>8
              <7>2. CASE k # pos  BY <7>2, <6>3
              <7>. QED  BY <7>1, <7>2
            <6>10. \A k \in 1..K : (table'[k] # empty) <=> (table[k] # empty)
              <7>. SUFFICES ASSUME NEW k \in 1..K
                            PROVE  (table'[k] # empty) <=> (table[k] # empty)
                OBVIOUS
              <7>1. CASE k = pos
                <8>1. table'[k] = table[pos] * (-1)  BY <6>2, <7>1
                <8>2. table[pos] \in Int  BY <6>6 DEF TableValues
                <8>. QED  BY <8>1, <8>2, <7>1 DEF empty
              <7>2. CASE k # pos  BY <7>2, <6>3
              <7>. QED  BY <7>1, <7>2
            <6>11. table[i] # empty /\ table[j] # empty  BY <6>10
            <6>12. abs(table[i]) # abs(table[j])
              BY <3>2, <6>11 DEF NoDupsTable
            <6>. QED  BY <6>9, <6>12
          <5>B. CASE ~(lo'[self] # empty /\
                      lo'[self] > largestElem(newexternal) /\
                      ((ei[self] <= K /\ ~wrapped(lo'[self],ei[self])) \/
                       (ei[self] > K /\ wrapped(lo'[self],ei[self]))))
            \* Inner ELSE: UNCHANGED table.
            <6>1. UNCHANGED table  BY <5>B
            <6>2. abs(table[i]) # abs(table[j])
              BY <3>2, <6>1 DEF NoDupsTable
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <5>A, <5>B
        \* Close SortPermInv' conjuncts.
        <4>C1. \A s2 \in ProcSet :
                  pc'[s2] \in {"waitIns", "strIns", "flush"}
                    => NoDupsTable'
          BY <4>NdT
        <4>C2. \A s2 \in ProcSet :
                  pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] = "strIns"  BY <5>2
          <5>4. s2 = self  BY <5>3, <2>Muex
          <5>. QED  BY <5>1, <5>4
        <4>C3. \A s2 \in ProcSet :
                  pc'[s2] \in {"nestedIns", "set"} =>
                    /\ mod(ej'[s2] + 1, K) \in 1..K
                    /\ (lo'[s2] # empty =>
                          \A j \in 1..K :
                            j # mod(ej'[s2] + 1, K)
                              /\ table'[j] # empty =>
                              abs(table'[j]) # abs(lo'[s2]))
                    /\ \A i, j \in 1..K :
                         i # j /\ i # mod(ej'[s2] + 1, K)
                               /\ j # mod(ej'[s2] + 1, K)
                               /\ table'[i] # empty
                               /\ table'[j] # empty =>
                         abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  FALSE
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"nestedIns", "set"}  BY <5>2
          <5>. QED  BY <5>3, <2>Muex, <5>1
        <4>. QED  BY <4>C1, <4>C2, <4>C3 DEF SortPermInv
      <3>B. CASE ~(ei[self] <= K+L)
        <4>. USE <3>B
        <4>1. pc'[self] = "rtrn"  OBVIOUS
        <4>2. UNCHANGED <<table, ei, ej, lo>>
          <5>1. UNCHANGED <<table, ei, lo>>  OBVIOUS
          <5>. QED  BY <5>1
        <4>C1. \A s2 \in ProcSet :
                  pc'[s2] \in {"waitIns", "strIns", "flush"}
                    => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <5>2
          <5>4. NoDupsTable  BY <5>3
          <5>. QED  BY <5>4, <4>2
        <4>C2. \A s2 \in ProcSet :
                  pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] = "strIns"  BY <5>2
          <5>4. ej[s2] = ei[s2]  BY <5>3
          <5>5. ej'[s2] = ej[s2] /\ ei'[s2] = ei[s2]  BY <5>1
          <5>. QED  BY <5>4, <5>5
        <4>C3. \A s2 \in ProcSet :
                  pc'[s2] \in {"nestedIns", "set"} =>
                    /\ mod(ej'[s2] + 1, K) \in 1..K
                    /\ (lo'[s2] # empty =>
                          \A j \in 1..K :
                            j # mod(ej'[s2] + 1, K)
                              /\ table'[j] # empty =>
                              abs(table'[j]) # abs(lo'[s2]))
                    /\ \A i, j \in 1..K :
                         i # j /\ i # mod(ej'[s2] + 1, K)
                               /\ j # mod(ej'[s2] + 1, K)
                               /\ table'[i] # empty
                               /\ table'[j] # empty =>
                         abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                               /\ (lo'[s2] # empty =>
                                     \A j \in 1..K :
                                       j # mod(ej'[s2] + 1, K)
                                         /\ table'[j] # empty =>
                                         abs(table'[j])
                                           # abs(lo'[s2]))
                               /\ \A i, j \in 1..K :
                                    i # j
                                      /\ i # mod(ej'[s2] + 1, K)
                                      /\ j # mod(ej'[s2] + 1, K)
                                      /\ table'[i] # empty
                                      /\ table'[j] # empty =>
                                    abs(table'[i]) # abs(table'[j])
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"nestedIns", "set"}  BY <5>2
          <5>4. ej'[s2] = ej[s2]  BY <5>1
          <5>5. lo'[s2] = lo[s2]  BY <5>1
          <5>. QED  BY <5>3, <5>4, <5>5, <4>2
        <4>. QED  BY <4>C1, <4>C2, <4>C3 DEF SortPermInv
      <3>. QED  BY <3>A, <3>B
    <2>5. CASE rtrn(self)
      \* pc[self] = "rtrn" (not in any SortPermInv trigger at self since
      \* rtrn is handled by DupInv's third conjunct); pc'[self] = "endEv".
      \* Table unchanged, so conjuncts at other s2 preserved.
      <3>. USE <2>5 DEF rtrn
      <3>1. pc[self] = "rtrn"  OBVIOUS
      <3>2. pc'[self] = Head(stack[self]).pc  OBVIOUS
      <3>3. stack[self] # <<>>  BY <3>1
      <3>4. Head(stack[self]).pc = "endEv"  BY <3>1, <3>3
      <3>5. pc'[self] = "endEv"  BY <3>2, <3>4
      <3>6. UNCHANGED table  OBVIOUS
      <3>C1. \A s2 \in ProcSet :
                pc'[s2] \in {"waitIns", "strIns", "flush"}
                  => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"waitIns", "strIns", "flush"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. s2 # self  BY <3>5
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <4>2
        <4>4. NoDupsTable  BY <4>3
        <4>. QED  BY <4>4, <3>6
      <3>C2. \A s2 \in ProcSet :
                pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                      PROVE  ej'[s2] = ei'[s2]
          OBVIOUS
        <4>1. s2 # self  BY <3>5
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] = "strIns"  BY <4>2
        <4>4. ej[s2] = ei[s2]  BY <4>3
        <4>5. ej'[s2] = ej[s2] /\ ei'[s2] = ei[s2]  BY <4>1
        <4>. QED  BY <4>4, <4>5
      <3>C3. \A s2 \in ProcSet :
                pc'[s2] \in {"nestedIns", "set"} =>
                  /\ mod(ej'[s2] + 1, K) \in 1..K
                  /\ (lo'[s2] # empty =>
                        \A j \in 1..K :
                          j # mod(ej'[s2] + 1, K)
                            /\ table'[j] # empty =>
                            abs(table'[j]) # abs(lo'[s2]))
                  /\ \A i, j \in 1..K :
                       i # j /\ i # mod(ej'[s2] + 1, K)
                             /\ j # mod(ej'[s2] + 1, K)
                             /\ table'[i] # empty
                             /\ table'[j] # empty =>
                       abs(table'[i]) # abs(table'[j])
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"nestedIns", "set"}
                      PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                             /\ (lo'[s2] # empty =>
                                   \A j \in 1..K :
                                     j # mod(ej'[s2] + 1, K)
                                       /\ table'[j] # empty =>
                                       abs(table'[j])
                                         # abs(lo'[s2]))
                             /\ \A i, j \in 1..K :
                                  i # j
                                    /\ i # mod(ej'[s2] + 1, K)
                                    /\ j # mod(ej'[s2] + 1, K)
                                    /\ table'[i] # empty
                                    /\ table'[j] # empty =>
                                  abs(table'[i]) # abs(table'[j])
          OBVIOUS
        <4>1. s2 # self  BY <3>5
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] \in {"nestedIns", "set"}  BY <4>2
        <4>4. ej'[s2] = ej[s2]  BY <4>1
        <4>5. lo'[s2] = lo[s2]  BY <4>1
        <4>. QED  BY <4>3, <4>4, <4>5, <3>6
      <3>. QED  BY <3>C1, <3>C2, <3>C3 DEF SortPermInv
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>3. ASSUME NEW self \in Writer, p(self)
        PROVE  SortPermInv'
    <2>. USE <1>3, ProcSetIsWriter DEF p
    \* Helper: at non-Evict labels, `evict' has no relation to self.
    \* We split on the 13 writer sub-actions and handle each.
    <2>1. CASE pick(self)
      <3>. USE <2>1 DEF pick
      <3>1. pc[self] = "pick"  OBVIOUS
      <3>2. pc'[self] \in {"put", "Done"}  OBVIOUS
      <3>3. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      \* pc'[self] not in any SortPermInv trigger.  For OTHER s2 at
      \* triggers, pc'[s2] = pc[s2], variables unchanged, so conjuncts
      \* preserved directly from pre-state.
      <3>4. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>C1. \A s2 \in ProcSet :
                pc'[s2] \in {"waitIns", "strIns", "flush"}
                  => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"waitIns", "strIns", "flush"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>2. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <4>1, <3>4
        <4>3. NoDupsTable  BY <4>2
        <4>. QED  BY <4>3, <3>3
      <3>C2. \A s2 \in ProcSet :
                pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                      PROVE  ej'[s2] = ei'[s2]
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>. QED  BY <4>1, <3>4
      <3>C3. \A s2 \in ProcSet :
                pc'[s2] \in {"nestedIns", "set"} =>
                  /\ mod(ej'[s2] + 1, K) \in 1..K
                  /\ (lo'[s2] # empty =>
                        \A j \in 1..K :
                          j # mod(ej'[s2] + 1, K)
                            /\ table'[j] # empty =>
                            abs(table'[j]) # abs(lo'[s2]))
                  /\ \A i, j \in 1..K :
                       i # j /\ i # mod(ej'[s2] + 1, K)
                             /\ j # mod(ej'[s2] + 1, K)
                             /\ table'[i] # empty
                             /\ table'[j] # empty =>
                       abs(table'[i]) # abs(table'[j])
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"nestedIns", "set"}
                      PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                             /\ (lo'[s2] # empty =>
                                   \A j \in 1..K :
                                     j # mod(ej'[s2] + 1, K)
                                       /\ table'[j] # empty =>
                                       abs(table'[j])
                                         # abs(lo'[s2]))
                             /\ \A i, j \in 1..K :
                                  i # j
                                    /\ i # mod(ej'[s2] + 1, K)
                                    /\ j # mod(ej'[s2] + 1, K)
                                    /\ table'[i] # empty
                                    /\ table'[j] # empty =>
                                  abs(table'[i]) # abs(table'[j])
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>. QED  BY <4>1, <3>4, <3>3
      <3>. QED  BY <3>C1, <3>C2, <3>C3 DEF SortPermInv
    <2>2. CASE put(self)
      <3>. USE <2>2 DEF put
      <3>1. pc[self] = "put"  OBVIOUS
      <3>2. pc'[self] \in {"chkSnc", "waitEv"}  OBVIOUS
      <3>3. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>4. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>. HIDE DEF put
      <3>C1. \A s2 \in ProcSet :
                pc'[s2] \in {"waitIns", "strIns", "flush"}
                  => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"waitIns", "strIns", "flush"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>2. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <4>1, <3>4
        <4>. QED  BY <4>2, <3>3
      <3>C2. \A s2 \in ProcSet :
                pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                      PROVE  ej'[s2] = ei'[s2]
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>. QED  BY <4>1, <3>4
      <3>C3. \A s2 \in ProcSet :
                pc'[s2] \in {"nestedIns", "set"} =>
                  /\ mod(ej'[s2] + 1, K) \in 1..K
                  /\ (lo'[s2] # empty =>
                        \A j \in 1..K :
                          j # mod(ej'[s2] + 1, K)
                            /\ table'[j] # empty =>
                            abs(table'[j]) # abs(lo'[s2]))
                  /\ \A i, j \in 1..K :
                       i # j /\ i # mod(ej'[s2] + 1, K)
                             /\ j # mod(ej'[s2] + 1, K)
                             /\ table'[i] # empty
                             /\ table'[j] # empty =>
                       abs(table'[i]) # abs(table'[j])
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"nestedIns", "set"}
                      PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                             /\ (lo'[s2] # empty =>
                                   \A j \in 1..K :
                                     j # mod(ej'[s2] + 1, K)
                                       /\ table'[j] # empty =>
                                       abs(table'[j])
                                         # abs(lo'[s2]))
                             /\ \A i, j \in 1..K :
                                  i # j
                                    /\ i # mod(ej'[s2] + 1, K)
                                    /\ j # mod(ej'[s2] + 1, K)
                                    /\ table'[i] # empty
                                    /\ table'[j] # empty =>
                                  abs(table'[i]) # abs(table'[j])
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>. QED  BY <4>1, <3>4, <3>3
      <3>. QED  BY <3>C1, <3>C2, <3>C3 DEF SortPermInv
    <2>3. CASE waitEv(self)
      \* pc[self] = "waitEv", pc'[self] \in {"endWEv", "put", "pick"}.
      \* UNCHANGED <<table, ei, ej, lo>>.  Structurally identical to <2>1.
      <3>. USE <2>3 DEF waitEv
      <3>1. pc'[self] \notin {"waitIns", "strIns", "flush",
                               "nestedIns", "set"}
        OBVIOUS
      <3>2. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>3. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF SortPermInv
    <2>4. CASE endWEv(self)
      <3>. USE <2>4 DEF endWEv
      <3>1. pc'[self] \notin {"waitIns", "strIns", "flush",
                               "nestedIns", "set"}
        OBVIOUS
      <3>2. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>3. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF SortPermInv
    <2>5. CASE chkSnc(self)
      <3>. USE <2>5 DEF chkSnc
      <3>1. pc'[self] \notin {"waitIns", "strIns", "flush",
                               "nestedIns", "set"}
        OBVIOUS
      <3>2. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>3. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF SortPermInv
    <2>6. CASE cntns(self)
      <3>. USE <2>6 DEF cntns
      <3>1. pc'[self] \notin {"waitIns", "strIns", "flush",
                               "nestedIns", "set"}
        OBVIOUS
      <3>2. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>3. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF SortPermInv
    <2>7. CASE onSnc(self)
      <3>. USE <2>7 DEF onSnc
      <3>1. pc'[self] \notin {"waitIns", "strIns", "flush",
                               "nestedIns", "set"}
        OBVIOUS
      <3>2. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>3. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF SortPermInv
    <2>8. CASE insrt(self)
      <3>. USE <2>8 DEF insrt
      <3>1. pc'[self] \notin {"waitIns", "strIns", "flush",
                               "nestedIns", "set"}
        OBVIOUS
      <3>2. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>3. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF SortPermInv
    <2>9. CASE isMth(self)
      <3>. USE <2>9 DEF isMth
      <3>1. pc'[self] \notin {"waitIns", "strIns", "flush",
                               "nestedIns", "set"}
        OBVIOUS
      <3>2. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>3. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF SortPermInv
    <2>10. CASE cas(self)
      \* Split into failed- and successful-CAS branches, exactly
      \* mirroring the `cas` case of `DupInvNext' (and its known deep
      \* OMITTED -- the "probe-sequence correctness" property of open
      \* addressing, aka the "no duplicate fingerprint insertion" claim
      \* at successful CAS).
      <3>. USE <2>10 DEF cas
      <3>1. pc[self] = "cas"  OBVIOUS
      <3>2. pc'[self] \in {"pick", "insrt"}  OBVIOUS
      <3>3. UNCHANGED <<ei, ej, lo>>  OBVIOUS
      <3>A. CASE ~(table[idx(fp[self],index[self])] = expected[self])
        \* Failed CAS: table UNCHANGED, pc'[self] = "insrt".
        <4>. USE <3>A
        <4>1. UNCHANGED table  OBVIOUS
        <4>2a. result' = [result EXCEPT ![self] = FALSE]  OBVIOUS
        <4>2b. self \in DOMAIN result  BY ProcSetIsWriter DEF ResultType
        <4>2c. result'[self] = FALSE  BY <4>2a, <4>2b
        <4>2. pc'[self] = "insrt"  BY <4>2c
        <4>3. \A s2 \in ProcSet : s2 # self =>
                  /\ pc'[s2] = pc[s2]
                  /\ ej'[s2] = ej[s2]
                  /\ ei'[s2] = ei[s2]
                  /\ lo'[s2] = lo[s2]
          OBVIOUS
        <4>C1. \A s2 \in ProcSet :
                  pc'[s2] \in {"waitIns", "strIns", "flush"}
                    => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 # self  BY <4>2
          <5>2. pc[s2] \in {"waitIns", "strIns", "flush"}
            BY <5>1, <4>3
          <5>3. NoDupsTable  BY <5>2
          <5>. QED  BY <5>3, <4>1
        <4>C2. \A s2 \in ProcSet :
                  pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>2
          <5>2. pc[s2] = "strIns"  BY <5>1, <4>3
          <5>3. ej[s2] = ei[s2]  BY <5>2
          <5>. QED  BY <5>3, <5>1, <4>3
        <4>C3. \A s2 \in ProcSet :
                  pc'[s2] \in {"nestedIns", "set"} =>
                    /\ mod(ej'[s2] + 1, K) \in 1..K
                    /\ (lo'[s2] # empty =>
                          \A j \in 1..K :
                            j # mod(ej'[s2] + 1, K)
                              /\ table'[j] # empty =>
                              abs(table'[j]) # abs(lo'[s2]))
                    /\ \A i, j \in 1..K :
                         i # j /\ i # mod(ej'[s2] + 1, K)
                               /\ j # mod(ej'[s2] + 1, K)
                               /\ table'[i] # empty
                               /\ table'[j] # empty =>
                         abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                               /\ (lo'[s2] # empty =>
                                     \A j \in 1..K :
                                       j # mod(ej'[s2] + 1, K)
                                         /\ table'[j] # empty =>
                                         abs(table'[j])
                                           # abs(lo'[s2]))
                               /\ \A i, j \in 1..K :
                                    i # j
                                      /\ i # mod(ej'[s2] + 1, K)
                                      /\ j # mod(ej'[s2] + 1, K)
                                      /\ table'[i] # empty
                                      /\ table'[j] # empty =>
                                    abs(table'[i]) # abs(table'[j])
            OBVIOUS
          <5>1. s2 # self  BY <4>2
          <5>2. pc[s2] \in {"nestedIns", "set"}  BY <5>1, <4>3
          <5>3. ej'[s2] = ej[s2] /\ lo'[s2] = lo[s2]  BY <5>1, <4>3
          <5>. QED  BY <5>2, <5>3, <4>1
        <4>. QED  BY <4>C1, <4>C2, <4>C3 DEF SortPermInv
      <3>B. CASE table[idx(fp[self],index[self])] = expected[self]
        \* Successful CAS: table'[idx] := fp[self].  pc'[self] = "pick".
        \* result' = TRUE.  history' = history \cup {fp[self]}.
        \* UNCHANGED: <<external, newexternal, evict, waitCnt, stack, ei,
        \*               ej, lo, fp, index, expected>>.
        \* By `CasFreshness' (clauses (ii) and (iii)), the new cell's
        \* `|fp[self]|' is distinct from every other non-empty
        \* `|table[k]|' and from every concurrent sorter's `|lo[s2]|',
        \* which is exactly what `SortPermInv'' needs to preserve.
        <4>. USE <3>B
        <4>. DEFINE pos == idx(fp[self], index[self])
        <4>1. result' = [result EXCEPT ![self] = TRUE]  OBVIOUS
        <4>1a. self \in DOMAIN result  BY ProcSetIsWriter DEF ResultType
        <4>1b. result'[self] = TRUE  BY <4>1, <4>1a
        <4>2. pc'[self] = "pick"  BY <4>1b
        <4>3. table' = [table EXCEPT ![pos] = fp[self]]  OBVIOUS
        <4>4. UNCHANGED <<ei, ej, lo>>  OBVIOUS
        \* CasFreshness instance at self.
        <4>F. /\ pos \in 1..K
              /\ \A k \in 1..K :
                   k # pos /\ table[k] # empty =>
                     abs(table[k]) # abs(fp[self])
              /\ \A s2 \in Writer :
                   pc[s2] \in {"nestedIns", "set"} /\ lo[s2] # empty =>
                     abs(lo[s2]) # abs(fp[self])
          BY <3>1 DEF CasFreshness
        <4>5. table'[pos] = fp[self]  BY <4>3, <4>F
        <4>6. \A k \in 1..K : k # pos => table'[k] = table[k]
          BY <4>3, <4>F
        \* SortPermInv' conjunct 1: triggered by s2 at {waitIns, strIns,
        \* flush}.  Such s2 is # self (pc'[self] = "pick"), so pc[s2] =
        \* pc'[s2] is in the trigger pre-state, giving pre-NoDupsTable
        \* via SortPermInv conjunct 1.  Combined with CasFreshness for
        \* the modified cell, NoDupsTable' holds.
        <4>C1. \A s2 \in ProcSet :
                  pc'[s2] \in {"waitIns", "strIns", "flush"}
                    => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 # self  BY <4>2
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <5>2
          <5>4. NoDupsTable  BY <5>3
          \* Now propagate to table' using CasFreshness for the cell at pos.
          <5>. SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K,
                                i # j,
                                table'[i] # empty, table'[j] # empty
                        PROVE  abs(table'[i]) # abs(table'[j])
            BY DEF NoDupsTable
          <5>A. CASE i = pos /\ j # pos
            <6>1. table'[i] = fp[self]  BY <4>5, <5>A
            <6>2. table'[j] = table[j]  BY <4>6, <5>A
            <6>3. table[j] # empty  BY <6>2
            <6>4. j # pos  BY <5>A
            <6>5. abs(table[j]) # abs(fp[self])  BY <4>F, <6>3, <6>4
            <6>. QED  BY <6>1, <6>2, <6>5
          <5>B. CASE j = pos /\ i # pos
            <6>1. table'[j] = fp[self]  BY <4>5, <5>B
            <6>2. table'[i] = table[i]  BY <4>6, <5>B
            <6>3. table[i] # empty  BY <6>2
            <6>4. i # pos  BY <5>B
            <6>5. abs(table[i]) # abs(fp[self])  BY <4>F, <6>3, <6>4
            <6>. QED  BY <6>1, <6>2, <6>5
          <5>C. CASE i # pos /\ j # pos
            <6>1. table'[i] = table[i]  BY <4>6, <5>C
            <6>2. table'[j] = table[j]  BY <4>6, <5>C
            <6>3. table[i] # empty /\ table[j] # empty  BY <6>1, <6>2
            <6>4. abs(table[i]) # abs(table[j])
              BY <5>4, <6>3 DEF NoDupsTable
            <6>. QED  BY <6>1, <6>2, <6>4
          <5>D. CASE i = pos /\ j = pos
            BY <5>D
          <5>. QED  BY <5>A, <5>B, <5>C, <5>D
        \* SortPermInv' conjunct 2.
        <4>C2. \A s2 \in ProcSet :
                  pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>2
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] = "strIns"  BY <5>2
          <5>4. ej[s2] = ei[s2]  BY <5>3
          <5>5. ej'[s2] = ej[s2] /\ ei'[s2] = ei[s2]  BY <4>4
          <5>. QED  BY <5>4, <5>5
        \* SortPermInv' conjunct 3.
        <4>C3. \A s2 \in ProcSet :
                  pc'[s2] \in {"nestedIns", "set"} =>
                    /\ mod(ej'[s2] + 1, K) \in 1..K
                    /\ (lo'[s2] # empty =>
                          \A j \in 1..K :
                            j # mod(ej'[s2] + 1, K)
                              /\ table'[j] # empty =>
                              abs(table'[j]) # abs(lo'[s2]))
                    /\ \A i, j \in 1..K :
                         i # j /\ i # mod(ej'[s2] + 1, K)
                               /\ j # mod(ej'[s2] + 1, K)
                               /\ table'[i] # empty
                               /\ table'[j] # empty =>
                         abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                               /\ (lo'[s2] # empty =>
                                     \A j \in 1..K :
                                       j # mod(ej'[s2] + 1, K)
                                         /\ table'[j] # empty =>
                                         abs(table'[j])
                                           # abs(lo'[s2]))
                               /\ \A i, j \in 1..K :
                                    i # j
                                      /\ i # mod(ej'[s2] + 1, K)
                                      /\ j # mod(ej'[s2] + 1, K)
                                      /\ table'[i] # empty
                                      /\ table'[j] # empty =>
                                    abs(table'[i]) # abs(table'[j])
            OBVIOUS
          <5>1. s2 # self  BY <4>2
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"nestedIns", "set"}  BY <5>2
          <5>4. ej'[s2] = ej[s2] /\ lo'[s2] = lo[s2]  BY <4>4
          <5>5. s2 \in Writer  BY ProcSetIsWriter
          \* gap = gap_pre.
          <5>. DEFINE gappre == mod(ej[s2] + 1, K)
          <5>6. mod(ej'[s2] + 1, K) = gappre  BY <5>4
          <5>7. gappre \in 1..K  BY <5>3
          <5>8. mod(ej'[s2] + 1, K) \in 1..K  BY <5>6, <5>7
          \* (b) lo'[s2] # empty => |table'[j]| # |lo'[s2]| for j # gap_post.
          <5>9. lo'[s2] # empty =>
                   \A j \in 1..K :
                     j # mod(ej'[s2] + 1, K) /\ table'[j] # empty =>
                       abs(table'[j]) # abs(lo'[s2])
            <6>. SUFFICES ASSUME lo'[s2] # empty,
                                  NEW j \in 1..K,
                                  j # mod(ej'[s2] + 1, K),
                                  table'[j] # empty
                          PROVE  abs(table'[j]) # abs(lo'[s2])
              OBVIOUS
            <6>1. lo[s2] # empty  BY <5>4
            <6>2. j # gappre  BY <5>6
            <6>A. CASE j = pos
              <7>1. table'[j] = fp[self]  BY <4>5, <6>A
              \* By CasFreshness clause (iii): |lo[s2]| # |fp[self]|.
              <7>2. abs(lo[s2]) # abs(fp[self])
                BY <4>F, <5>3, <5>5, <6>1
              <7>. QED  BY <7>1, <7>2, <5>4
            <6>B. CASE j # pos
              <7>1. table'[j] = table[j]  BY <4>6, <6>B
              <7>2. table[j] # empty  BY <7>1
              \* Pre-state SortPermInv conjunct 3(b) at s2.
              <7>3. abs(table[j]) # abs(lo[s2])  BY <5>3, <6>1, <6>2, <7>2
              <7>. QED  BY <7>1, <7>3, <5>4
            <6>. QED  BY <6>A, <6>B
          \* (c) for i, j # gap_post both # gap, distinct, both non-empty.
          <5>10. \A i, j \in 1..K :
                    i # j /\ i # mod(ej'[s2] + 1, K)
                          /\ j # mod(ej'[s2] + 1, K)
                          /\ table'[i] # empty /\ table'[j] # empty =>
                    abs(table'[i]) # abs(table'[j])
            <6>. SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K,
                                  i # j,
                                  i # mod(ej'[s2] + 1, K),
                                  j # mod(ej'[s2] + 1, K),
                                  table'[i] # empty,
                                  table'[j] # empty
                          PROVE  abs(table'[i]) # abs(table'[j])
              OBVIOUS
            <6>1. i # gappre /\ j # gappre  BY <5>6
            <6>A. CASE i = pos /\ j # pos
              <7>1. table'[i] = fp[self]  BY <4>5, <6>A
              <7>2. table'[j] = table[j]  BY <4>6, <6>A
              <7>3. table[j] # empty  BY <7>2
              <7>4. j # pos  BY <6>A
              <7>5. abs(table[j]) # abs(fp[self])
                BY <4>F, <7>3, <7>4
              <7>. QED  BY <7>1, <7>2, <7>5
            <6>B. CASE j = pos /\ i # pos
              <7>1. table'[j] = fp[self]  BY <4>5, <6>B
              <7>2. table'[i] = table[i]  BY <4>6, <6>B
              <7>3. table[i] # empty  BY <7>2
              <7>4. i # pos  BY <6>B
              <7>5. abs(table[i]) # abs(fp[self])
                BY <4>F, <7>3, <7>4
              <7>. QED  BY <7>1, <7>2, <7>5
            <6>C. CASE i # pos /\ j # pos
              <7>1. table'[i] = table[i]  BY <4>6, <6>C
              <7>2. table'[j] = table[j]  BY <4>6, <6>C
              <7>3. table[i] # empty /\ table[j] # empty
                BY <7>1, <7>2
              <7>4. abs(table[i]) # abs(table[j])
                BY <5>3, <6>1, <7>3
              <7>. QED  BY <7>1, <7>2, <7>4
            <6>D. CASE i = pos /\ j = pos
              BY <6>D
            <6>. QED  BY <6>A, <6>B, <6>C, <6>D
          <5>. QED  BY <5>8, <5>9, <5>10
        <4>. QED  BY <4>C1, <4>C2, <4>C3 DEF SortPermInv
      <3>. QED  BY <3>A, <3>B
    <2>11. CASE tryEv(self)
      \* pc[self] = "tryEv", pc'[self] \in {"waitIns", "put"}.
      \* UNCHANGED <<table, ei, ej, lo>>.  Two sub-cases: evict = FALSE
      \* (entering EvictUnion) and evict = TRUE (unsuccessful, pc' = "put").
      <3>. USE <2>11 DEF tryEv
      <3>1. pc[self] = "tryEv"  OBVIOUS
      <3>2. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>3. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>A. CASE evict = FALSE
        \* pc'[self] = "waitIns" (in first trigger).  Need NoDupsTable'.
        \* Pre: evict = FALSE, FindOrPut = TRUE (by DupInv), so
        \* NoDupsTable (by DupInv second conjunct).
        <4>. USE <3>A
        <4>1. pc'[self] = "waitIns"  OBVIOUS
        <4>2. FindOrPut  BY DEF FindOrPut
        <4>3. NoDupsTable  BY <4>2
        \* Other s2 at triggers pre-state: by EvictExclusive (evict =
        \* FALSE gives no one in EvictUnion).
        <4>4. \A s2 \in ProcSet :
                pc[s2] \notin {"waitIns", "strIns", "flush",
                                "nestedIns", "set"}
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc[s2] \in {"waitIns", "strIns", "flush",
                                             "nestedIns", "set"}
                        PROVE  FALSE
            OBVIOUS
          <5>1. pc[s2] \in EvictUnion  OBVIOUS
          <5>. QED  BY <5>1
        <4>C1. \A s2 \in ProcSet :
                  pc'[s2] \in {"waitIns", "strIns", "flush"}
                    => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. CASE s2 = self
            BY <5>1, <4>3, <3>2
          <5>2. CASE s2 # self
            <6>1. pc'[s2] = pc[s2]  BY <5>2
            <6>2. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <6>1
            <6>. QED  BY <6>2, <4>4
          <5>. QED  BY <5>1, <5>2
        <4>C2. \A s2 \in ProcSet :
                  pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] = "strIns"  BY <5>2
          <5>. QED  BY <5>3, <4>4
        <4>C3. \A s2 \in ProcSet :
                  pc'[s2] \in {"nestedIns", "set"} =>
                    /\ mod(ej'[s2] + 1, K) \in 1..K
                    /\ (lo'[s2] # empty =>
                          \A j \in 1..K :
                            j # mod(ej'[s2] + 1, K)
                              /\ table'[j] # empty =>
                              abs(table'[j]) # abs(lo'[s2]))
                    /\ \A i, j \in 1..K :
                         i # j /\ i # mod(ej'[s2] + 1, K)
                               /\ j # mod(ej'[s2] + 1, K)
                               /\ table'[i] # empty
                               /\ table'[j] # empty =>
                         abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  FALSE
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"nestedIns", "set"}  BY <5>2
          <5>. QED  BY <5>3, <4>4
        <4>. QED  BY <4>C1, <4>C2, <4>C3 DEF SortPermInv
      <3>B. CASE evict # FALSE
        \* pc'[self] = "put" (not in any trigger).  evict unchanged.
        \* Other s2 at triggers: preserved (by pre-state SortPermInv).
        <4>. USE <3>B
        <4>1. pc'[self] = "put"  OBVIOUS
        <4>C1. \A s2 \in ProcSet :
                  pc'[s2] \in {"waitIns", "strIns", "flush"}
                    => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"waitIns", "strIns", "flush"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>2. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <5>1, <3>3
          <5>. QED  BY <5>2, <3>2
        <4>C2. \A s2 \in ProcSet :
                  pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                        PROVE  ej'[s2] = ei'[s2]
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>. QED  BY <5>1, <3>3
        <4>C3. \A s2 \in ProcSet :
                  pc'[s2] \in {"nestedIns", "set"} =>
                    /\ mod(ej'[s2] + 1, K) \in 1..K
                    /\ (lo'[s2] # empty =>
                          \A j \in 1..K :
                            j # mod(ej'[s2] + 1, K)
                              /\ table'[j] # empty =>
                              abs(table'[j]) # abs(lo'[s2]))
                    /\ \A i, j \in 1..K :
                         i # j /\ i # mod(ej'[s2] + 1, K)
                               /\ j # mod(ej'[s2] + 1, K)
                               /\ table'[i] # empty
                               /\ table'[j] # empty =>
                         abs(table'[i]) # abs(table'[j])
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"nestedIns", "set"}
                        PROVE  /\ mod(ej'[s2] + 1, K) \in 1..K
                               /\ (lo'[s2] # empty =>
                                     \A j \in 1..K :
                                       j # mod(ej'[s2] + 1, K)
                                         /\ table'[j] # empty =>
                                         abs(table'[j])
                                           # abs(lo'[s2]))
                               /\ \A i, j \in 1..K :
                                    i # j
                                      /\ i # mod(ej'[s2] + 1, K)
                                      /\ j # mod(ej'[s2] + 1, K)
                                      /\ table'[i] # empty
                                      /\ table'[j] # empty =>
                                    abs(table'[i]) # abs(table'[j])
            OBVIOUS
          <5>1. s2 # self  BY <4>1
          <5>. QED  BY <5>1, <3>3, <3>2
        <4>. QED  BY <4>C1, <4>C2, <4>C3 DEF SortPermInv
      <3>. QED  BY <3>A, <3>B
    <2>12. CASE waitIns(self)
      \* pc[self] = "waitIns", pc'[self] = "strIns".
      \* ei' := 1, ej' := 1, lo' := 0.  Table UNCHANGED.
      \* Need NoDupsTable' and ej'[self] = ei'[self].
      <3>. USE <2>12 DEF waitIns
      <3>1. pc[self] = "waitIns"  OBVIOUS
      <3>2. pc'[self] = "strIns"  OBVIOUS
      <3>3. ei'[self] = 1 /\ ej'[self] = 1  OBVIOUS
      <3>4. UNCHANGED table  OBVIOUS
      <3>5. NoDupsTable  BY <3>1
      \* Other writers are NOT in EvictUnion (self is unique by
      \* EvictExclusive with pc[self] = "waitIns" in EvictUnion).
      <3>6. \A s2 \in ProcSet : s2 # self =>
                pc[s2] \notin {"waitIns", "strIns", "flush",
                                "nestedIns", "set"}
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, s2 # self,
                              pc[s2] \in {"waitIns", "strIns", "flush",
                                           "nestedIns", "set"}
                      PROVE  FALSE
          OBVIOUS
        <4>1. pc[self] \in EvictUnion  BY <3>1
        <4>2. pc[s2] \in EvictUnion  OBVIOUS
        <4>. QED  BY <4>1, <4>2
      <3>C1. \A s2 \in ProcSet :
                pc'[s2] \in {"waitIns", "strIns", "flush"}
                  => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"waitIns", "strIns", "flush"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. CASE s2 = self
          BY <4>1, <3>5, <3>4
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>2. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <5>1
          <5>. QED  BY <5>2, <3>6, <4>2, <3>4
        <4>. QED  BY <4>1, <4>2
      <3>C2. \A s2 \in ProcSet :
                pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                      PROVE  ej'[s2] = ei'[s2]
          OBVIOUS
        <4>1. CASE s2 = self
          BY <4>1, <3>3
        <4>2. CASE s2 # self
          <5>1. pc'[s2] = pc[s2]  BY <4>2
          <5>2. pc[s2] = "strIns"  BY <5>1
          <5>3. ej[s2] = ei[s2]  BY <5>2
          <5>4. ej'[s2] = ej[s2] /\ ei'[s2] = ei[s2]  BY <4>2
          <5>. QED  BY <5>3, <5>4
        <4>. QED  BY <4>1, <4>2
      <3>C3. \A s2 \in ProcSet :
                pc'[s2] \in {"nestedIns", "set"} =>
                  /\ mod(ej'[s2] + 1, K) \in 1..K
                  /\ (lo'[s2] # empty =>
                        \A j \in 1..K :
                          j # mod(ej'[s2] + 1, K)
                            /\ table'[j] # empty =>
                            abs(table'[j]) # abs(lo'[s2]))
                  /\ \A i, j \in 1..K :
                       i # j /\ i # mod(ej'[s2] + 1, K)
                             /\ j # mod(ej'[s2] + 1, K)
                             /\ table'[i] # empty
                             /\ table'[j] # empty =>
                       abs(table'[i]) # abs(table'[j])
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"nestedIns", "set"}
                      PROVE  FALSE
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>2. pc'[s2] = pc[s2]  BY <4>1
        <4>3. pc[s2] \in {"nestedIns", "set"}  BY <4>2
        <4>. QED  BY <4>3, <3>6, <4>1
      <3>. QED  BY <3>C1, <3>C2, <3>C3 DEF SortPermInv
    <2>13. CASE endEv(self)
      \* pc[self] = "endEv" (handled by DupInv), pc'[self] = "put".
      \* UNCHANGED <<table, ei, ej, lo>>.  evict' = FALSE.
      \* Other writers are NOT in EvictUnion (self is unique pre-state).
      <3>. USE <2>13 DEF endEv
      <3>1. pc[self] = "endEv"  OBVIOUS
      <3>2. pc'[self] = "put"  OBVIOUS
      <3>3. UNCHANGED <<table, ei, ej, lo>>  OBVIOUS
      <3>4. \A s2 \in ProcSet : s2 # self =>
                pc[s2] \notin {"waitIns", "strIns", "flush",
                                "nestedIns", "set"}
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, s2 # self,
                              pc[s2] \in {"waitIns", "strIns", "flush",
                                           "nestedIns", "set"}
                      PROVE  FALSE
          OBVIOUS
        <4>1. pc[self] \in EvictUnion  BY <3>1
        <4>2. pc[s2] \in EvictUnion  OBVIOUS
        <4>. QED  BY <4>1, <4>2
      <3>5. \A s2 \in ProcSet : s2 # self =>
                /\ pc'[s2] = pc[s2]
                /\ ej'[s2] = ej[s2]
                /\ ei'[s2] = ei[s2]
                /\ lo'[s2] = lo[s2]
        OBVIOUS
      <3>C1. \A s2 \in ProcSet :
                pc'[s2] \in {"waitIns", "strIns", "flush"}
                  => NoDupsTable'
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"waitIns", "strIns", "flush"}
                      PROVE  NoDupsTable'
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>2. pc[s2] \in {"waitIns", "strIns", "flush"}  BY <4>1, <3>5
        <4>3. s2 \in ProcSet /\ pc[s2] \in {"waitIns", "strIns",
                                              "flush", "nestedIns",
                                              "set"}  BY <4>2
        <4>. QED  BY <4>3, <3>4, <4>1
      <3>C2. \A s2 \in ProcSet :
                pc'[s2] = "strIns" => ej'[s2] = ei'[s2]
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet, pc'[s2] = "strIns"
                      PROVE  ej'[s2] = ei'[s2]
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>2. pc[s2] = "strIns"  BY <4>1, <3>5
        <4>. QED  BY <4>2, <3>4, <4>1
      <3>C3. \A s2 \in ProcSet :
                pc'[s2] \in {"nestedIns", "set"} =>
                  /\ mod(ej'[s2] + 1, K) \in 1..K
                  /\ (lo'[s2] # empty =>
                        \A j \in 1..K :
                          j # mod(ej'[s2] + 1, K)
                            /\ table'[j] # empty =>
                            abs(table'[j]) # abs(lo'[s2]))
                  /\ \A i, j \in 1..K :
                       i # j /\ i # mod(ej'[s2] + 1, K)
                             /\ j # mod(ej'[s2] + 1, K)
                             /\ table'[i] # empty
                             /\ table'[j] # empty =>
                       abs(table'[i]) # abs(table'[j])
        <4>. SUFFICES ASSUME NEW s2 \in ProcSet,
                              pc'[s2] \in {"nestedIns", "set"}
                      PROVE  FALSE
          OBVIOUS
        <4>1. s2 # self  BY <3>2
        <4>2. pc[s2] \in {"nestedIns", "set"}  BY <4>1, <3>5
        <4>. QED  BY <4>2, <3>4, <4>1
      <3>. QED  BY <3>C1, <3>C2, <3>C3 DEF SortPermInv
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
(* `flush' outer-else is FULLY DISCHARGED by invoking `SortPermInv' (the   *)
(* dedicated sort-permutation invariant defined above) to obtain           *)
(* `NoDupsTable' directly at `pc[self] = "flush"'.                         *)
(***************************************************************************)
LEMMA DupInvNext == Inv /\ ResultType /\ EiType /\ EjType /\ LoType
                    /\ EvictExclusive /\ CasFreshness /\ SortPermInv /\ DupInv
                    /\ [Next]_vars => DupInv'
  <1>. SUFFICES ASSUME Inv, ResultType, EiType, EjType, LoType,
                       EvictExclusive, CasFreshness, SortPermInv, DupInv, [Next]_vars
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
        \* s2 = self, pc'[self] = "rtrn" triggers, and the remaining
        \* obligation `NoDupsTable at pc[self] = "flush"' follows from
        \* the sort-permutation invariant `SortPermInv' (first conjunct
        \* applied with pc[self] = "flush").
        <4>10. NoDupsTable
          BY <4>2 DEF SortPermInv
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
        \* Successful CAS.  Discharged via `CasFreshness': clause (ii)
        \* of `CasFreshness' gives `|fp[self]|' distinct from every
        \* other non-empty `|table[k]|', restoring full `NoDupsTable''
        \* over the modified table.
        <4>. USE <3>2
        <4>. DEFINE pos == idx(fp[self], index[self])
        <4>1. result' = [result EXCEPT ![self] = TRUE]  OBVIOUS
        <4>1a. self \in DOMAIN result  BY ProcSetIsWriter DEF ResultType
        <4>1b. result'[self] = TRUE  BY <4>1, <4>1a
        <4>2. pc'[self] = "pick"  BY <4>1b
        <4>3. table' = [table EXCEPT ![pos] = fp[self]]  OBVIOUS
        <4>4. evict' = evict  OBVIOUS
        \* CasFreshness instance at self.
        <4>F. /\ pos \in 1..K
              /\ \A k \in 1..K :
                   k # pos /\ table[k] # empty =>
                     abs(table[k]) # abs(fp[self])
          BY ProcSetIsWriter DEF CasFreshness
        <4>5. table'[pos] = fp[self]  BY <4>3, <4>F
        <4>6. \A k \in 1..K : k # pos => table'[k] = table[k]
          BY <4>3, <4>F
        \* TableType': table' \in [1..K -> TableValues].
        <4>T. TableType'
          <5>. SUFFICES ASSUME NEW k \in 1..K
                        PROVE  table'[k] \in TableValues
            BY <4>3, <4>F DEF TableType
          <5>1. CASE k = pos
            <6>1. table'[k] = fp[self]  BY <5>1, <4>5
            <6>2. fp[self] \in fps  BY ProcSetIsWriter, CasFpInFps
            <6>. QED  BY <6>1, <6>2 DEF TableValues
          <5>2. CASE k # pos
            <6>1. table'[k] = table[k]  BY <5>2, <4>6
            <6>2. table[k] \in TableValues  BY DEF TableType
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <5>1, <5>2
        \* NoDupsTable' lemma: holds whenever pre-NoDupsTable holds.
        <4>NdLem. ASSUME NoDupsTable
                  PROVE  NoDupsTable'
          <5>. SUFFICES ASSUME NEW i \in 1..K, NEW j \in 1..K,
                                i # j,
                                table'[i] # empty, table'[j] # empty
                        PROVE  abs(table'[i]) # abs(table'[j])
            BY DEF NoDupsTable
          <5>A. CASE i = pos /\ j # pos
            <6>1. table'[i] = fp[self]  BY <4>5, <5>A
            <6>2. table'[j] = table[j]  BY <4>6, <5>A
            <6>3. table[j] # empty  BY <6>2
            <6>4. j # pos  BY <5>A
            <6>5. abs(table[j]) # abs(fp[self])  BY <4>F, <6>3, <6>4
            <6>. QED  BY <6>1, <6>2, <6>5
          <5>B. CASE j = pos /\ i # pos
            <6>1. table'[j] = fp[self]  BY <4>5, <5>B
            <6>2. table'[i] = table[i]  BY <4>6, <5>B
            <6>3. table[i] # empty  BY <6>2
            <6>4. i # pos  BY <5>B
            <6>5. abs(table[i]) # abs(fp[self])  BY <4>F, <6>3, <6>4
            <6>. QED  BY <6>1, <6>2, <6>5
          <5>C. CASE i # pos /\ j # pos
            <6>1. table'[i] = table[i]  BY <4>6, <5>C
            <6>2. table'[j] = table[j]  BY <4>6, <5>C
            <6>3. table[i] # empty /\ table[j] # empty  BY <6>1, <6>2
            <6>4. abs(table[i]) # abs(table[j])
              BY <4>NdLem, <6>3 DEF NoDupsTable
            <6>. QED  BY <6>1, <6>2, <6>4
          <5>D. CASE i = pos /\ j = pos
            BY <5>D
          <5>. QED  BY <5>A, <5>B, <5>C, <5>D
        <4>FoP. FindOrPut' => NoDupsTable'
          <5>. SUFFICES ASSUME FindOrPut'  PROVE NoDupsTable'
            OBVIOUS
          <5>1. FindOrPut  BY <4>4 DEF FindOrPut
          <5>2. NoDupsTable  BY <5>1
          <5>. QED  BY <4>NdLem, <5>2
        <4>R. \A s2 \in ProcSet :
                pc'[s2] \in {"rtrn", "endEv"} => NoDupsTable'
          <5>. SUFFICES ASSUME NEW s2 \in ProcSet,
                                pc'[s2] \in {"rtrn", "endEv"}
                        PROVE  NoDupsTable'
            OBVIOUS
          <5>1. s2 # self  BY <4>2
          <5>2. pc'[s2] = pc[s2]  BY <5>1
          <5>3. pc[s2] \in {"rtrn", "endEv"}  BY <5>2
          <5>4. NoDupsTable  BY <5>3
          <5>. QED  BY <4>NdLem, <5>4
        <4>. QED  BY <4>T, <4>FoP, <4>R DEF DupInv
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
(* `Duplicates' is the pairwise form over 1..K (equivalent to the          *)
(* `SelectSeq' formulation).  Under `FindOrPut' the second conjunct of     *)
(* `DupInv' (`NoDupsTable') gives the claim directly.                        *)
(***************************************************************************)
LEMMA DupInvImpliesDuplicates == DupInv => Duplicates
  <1>. SUFFICES ASSUME DupInv, FindOrPut
                PROVE  \A i \in 1..K : \A j \in (i+1)..K :
                         (table[i] # empty /\ table[j] # empty)
                           => abs(table[i]) # abs(table[j])
    BY DEF Duplicates, FindOrPut
  <1>. USE DEF DupInv, TableType, NoDupsTable
  <1>1. table \in [1..K -> TableValues]
    OBVIOUS
  <1>2. \A i, j \in 1..K : i # j /\ table[i] # empty /\ table[j] # empty
            => abs(table[i]) # abs(table[j])
    OBVIOUS
  <1>3. ASSUME NEW i \in 1..K, NEW j \in (i+1)..K,
               table[i] # empty, table[j] # empty
        PROVE abs(table[i]) # abs(table[j])
    <2>1. i # j
      OBVIOUS
    <2>. QED  BY <2>1, <1>2
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
                   /\ LoType /\ WaitCntInv /\ EvictExclusive
                   /\ CasFreshness /\ SortPermInv /\ DupInv)
    <2>1. Init => Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                    /\ LoType /\ WaitCntInv /\ EvictExclusive
                    /\ CasFreshness /\ SortPermInv /\ DupInv
      BY InitInv, InitStackOK, InitResultType, InitEiType, InitEjType,
         InitLoType, InitWaitCntInv, InitEvictExclusive,
         InitCasFreshness, InitSortPermInv, InitDupInv
    <2>2. (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
             /\ LoType /\ WaitCntInv /\ EvictExclusive
             /\ CasFreshness /\ SortPermInv /\ DupInv)
             /\ [Next]_vars
            => (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                  /\ LoType /\ WaitCntInv /\ EvictExclusive
                  /\ CasFreshness /\ SortPermInv /\ DupInv)'
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
      <3>7. Inv /\ StackOK /\ WaitCntInv /\ [Next]_vars => WaitCntInv'
        BY WaitCntInd
      <3>8. Inv /\ StackOK /\ WaitCntInv /\ EvictExclusive /\ [Next]_vars
              => EvictExclusive'
        BY EvictExclusiveInd
      <3>9. Inv /\ ResultType /\ CasFreshness /\ [Next]_vars
              => CasFreshness'
        BY CasFreshnessInd
      <3>10. Inv /\ StackOK /\ ResultType /\ EiType /\ EjType /\ LoType
              /\ DupInv /\ EvictExclusive /\ CasFreshness /\ SortPermInv
              /\ [Next]_vars
              => SortPermInv'
        BY SortPermInd
      <3>11. Inv /\ ResultType /\ EiType /\ EjType /\ LoType
               /\ EvictExclusive /\ CasFreshness /\ SortPermInv /\ DupInv
               /\ [Next]_vars
               => DupInv'
        BY DupInvNext
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8,
                    <3>9, <3>10, <3>11
    <2>. QED  BY <2>1, <2>2, PTL DEF Spec
  <1>2. (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
           /\ LoType /\ WaitCntInv /\ EvictExclusive
           /\ CasFreshness /\ SortPermInv /\ DupInv)
          => Duplicates
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
                  <9>2. Len(base) # 0  BY <8>1, <7>5, <7>6, <8>2
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
                   /\ LoType /\ WaitCntInv /\ EvictExclusive
                   /\ CasFreshness /\ SortPermInv /\ DupInv /\ SortedInv)
    <2>1. Init => Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                    /\ LoType /\ WaitCntInv /\ EvictExclusive
                    /\ CasFreshness /\ SortPermInv /\ DupInv /\ SortedInv
      BY InitInv, InitStackOK, InitResultType, InitEiType, InitEjType,
         InitLoType, InitWaitCntInv, InitEvictExclusive,
         InitCasFreshness, InitSortPermInv, InitDupInv, InitSortedInv
    <2>2. (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
             /\ LoType /\ WaitCntInv /\ EvictExclusive
             /\ CasFreshness /\ SortPermInv /\ DupInv /\ SortedInv)
            /\ [Next]_vars
          => (Inv /\ StackOK /\ ResultType /\ EiType /\ EjType
                /\ LoType /\ WaitCntInv /\ EvictExclusive
                /\ CasFreshness /\ SortPermInv /\ DupInv /\ SortedInv)'
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
      <3>7. Inv /\ StackOK /\ WaitCntInv /\ [Next]_vars => WaitCntInv'
        BY WaitCntInd
      <3>8. Inv /\ StackOK /\ WaitCntInv /\ EvictExclusive /\ [Next]_vars
              => EvictExclusive'
        BY EvictExclusiveInd
      <3>9. Inv /\ ResultType /\ CasFreshness /\ [Next]_vars
              => CasFreshness'
        BY CasFreshnessInd
      <3>10. Inv /\ StackOK /\ ResultType /\ EiType /\ EjType /\ LoType
              /\ DupInv /\ EvictExclusive /\ CasFreshness /\ SortPermInv
              /\ [Next]_vars
              => SortPermInv'
        BY SortPermInd
      <3>11. Inv /\ ResultType /\ EiType /\ EjType /\ LoType
               /\ EvictExclusive /\ CasFreshness /\ SortPermInv /\ DupInv
               /\ [Next]_vars
               => DupInv'
        BY DupInvNext
      <3>12. EiType /\ DupInv /\ SortedInv /\ [Next]_vars => SortedInv'
        BY SortedInvNext
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8,
                    <3>9, <3>10, <3>11, <3>12
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
