------------------------------ MODULE APCasInd ------------------------------
(* Finite-instance Apalache checks for the strengthened `CasFreshness' layer *)
(* `CasProbeUniqueAbsFp /\\ CasFreshnessCore' (the proof module conjoins them *)
(* as `CasFreshness').                                                        *)
(*                                                                            *)
(* Run (example depth 8; increase N for stronger bounded confidence):         *)
(*   apalache-mc check --length=N --config=APCasInd.cfg APCasInd.tla          *)
(*                                                                            *)
(* `ApalacheSpec' omits fairness conjuncts from `Spec' because Apalache's      *)
(* TLC config loader requires Init /\\ [][Next]_vars in canonical form.      *)

EXTENDS APOpenAddressing

(* Explicit alias for TLC / Apalache INVARIANT lines. *)
StrengthenedCasFresh == CasProbeUniqueAbsFp /\ CasFreshnessCore

(* Apalache expects a specification in canonical form Init /\\ [][Next]_vars *)
(* (fairness from OpenAddressing!Spec is not accepted by the config pass).     *)
ApalacheSpec == Init /\ [][Next]_vars

=============================================================================
