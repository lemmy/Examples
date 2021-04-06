------------------------------ MODULE Shutdown ------------------------------
EXTENDS Sequences, FiniteSets, Naturals

\* Define a new message type.
TrmMsg == [type |-> "trm"]

CONSTANT Nodes, Initiator, Messages
ASSUME /\ IsFiniteSet(Nodes) /\ Nodes # {}
       /\ Initiator \in Nodes
       /\ TrmMsg \in Messages

VARIABLES
 inbox
vars == <<inbox>>

Init ==
  /\ inbox \in [ Nodes -> Seq(Messages) ]

SendTermination(n) ==
  /\ n = Initiator
  \* Don't send termination message multiple times.  If - due to a
  \* cosmic ray - the initiator doesn't correctly terminate, don't
  \* let it interfere with future systems... 
  /\ \A j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type # "trm"
  \* Send termination message to all nodes (including self).
  /\ inbox' = [ node \in Nodes |-> inbox[node] \o <<TrmMsg>>]

(* Override with Sys.exit in PlusPy to gracefully terminate the runtime. *)
Terminate(n) == TRUE \*PrintT("sys.exit")

(*  *)
RecvTermination(n) ==
  /\ \E j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type = "trm"
  /\ Terminate(n)
  /\ UNCHANGED vars

Next(n) ==
  \/ SendTermination(n)
  \/ RecvTermination(n)

Spec ==
  Init /\ [][\E n \in Nodes: Next(n)]_vars
  
=============================================================================
