------------------------------ MODULE APCasInd ------------------------------
(* Finite-instance Apalache checks for the strengthened `CasFreshness' layer *)
(* `CasProbeUniqueAbsFp /\\ CasFreshnessCore' (the proof module conjoins them *)
(* as `CasFreshness').                                                        *)
(*                                                                            *)
(*--- Inductive invariant (Apalache running.md section 1.5; constants from cfg) *)
(* https://apalache-mc.org/docs/apalache/running.html#15-checking-an-inductive-invariant *)
(*                                                                            *)
(* IndInit:                                                                   *)
(*   apalache-mc check --config=APCasInd.cfg --init=Init                     *)
(*                      --inv=StrengthenedCasFresh --length=0 APCasInd.tla   *)
(*                                                                            *)
(* IndNext:                                                                   *)
(*   apalache-mc check --config=APCasInd.cfg --init=StrengthenedCasFresh      *)
(*                      --inv=StrengthenedCasFresh --length=1 APCasInd.tla    *)
(*                                                                            *)
(* Both report NoError for Apalache 0.57.0 here (finite domain + encoding).   *)
(* Bounded BMC (deeper traces, includes action inv if in cfg):                 *)
(*   apalache-mc check --length=k --config=APCasInd.cfg APCasInd.tla           *)
(*                                                                            *)
(* `ApalacheSpec' omits fairness conjuncts from `Spec' because Apalache's      *)
(* TLC config loader requires Init /\\ [][Next]_vars in canonical form.      *)

EXTENDS APOpenAddressing

(* Explicit alias for TLC / Apalache INVARIANT lines. *)
StrengthenedCasFresh == CasProbeUniqueAbsFp /\ CasFreshnessCore

(* Action-shaped inductive step: I(s) /\ s -> s' => I(s').  Apalache treats     *)
(* formulas with primes as action invariants (see invariants documentation).    *)
StrengthenedCasFreshInductiveStep ==
  StrengthenedCasFresh /\ Next => StrengthenedCasFresh'

(* Apalache expects a specification in canonical form Init /\\ [][Next]_vars *)
(* (fairness from OpenAddressing!Spec is not accepted by the config pass).     *)
ApalacheSpec == Init /\ [][Next]_vars

=============================================================================
