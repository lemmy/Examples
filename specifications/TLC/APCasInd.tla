------------------------------ MODULE APCasInd ------------------------------
(* Finite-instance Apalache checks for the strengthened `CasFreshness' layer *)
(* `CasProbeUniqueAbsFp /\\ CasFreshnessCore' (the proof module conjoins them *)
(* as `CasFreshness').                                                        *)
(*                                                                            *)
(* Run (example depth; increase k for stronger bounded confidence):          *)
(*   apalache-mc check --length=k --config=APCasInd.cfg APCasInd.tla          *)
(*                                                                            *)
(* `StrengthenedCasFresh' is a state invariant;                             *)
(* `StrengthenedCasFreshInductiveStep' is an action invariant (I /\\ Next =>   *)
(* I').  Apalache checks both along bounded symbolic runs from `Init'.  This  *)
(* is NOT the same as a full proof that I is inductive on the entire state   *)
(* space (e.g. unreachable I-states); for that use TLAPS or unbounded tools. *)
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
