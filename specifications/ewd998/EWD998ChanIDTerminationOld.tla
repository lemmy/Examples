---------------------- MODULE EWD998ChanIDTermination ----------------------
EXTENDS EWD998ChanID

\* Declare and define a new message type.
TrmMsg == [type |-> "trm"]
TMessage == Message \cup {TrmMsg}

\* Bound the number of tasks that each node executes (finite number of activations).
VARIABLES tasks
tvars == <<active, color, counter, inbox, tasks>>

------------------------------------------------------------------------------

TSendMsg(n) ==
  /\ SendMsg(n)
  /\ tasks[n] > 0
  /\ tasks' = [tasks EXCEPT ![n] = @ - 1]

(* Replaces SendMsg. *)
TEnvironment == 
  \E n \in Nodes : 
         \/ TSendMsg(n)
         \/ /\ RecvMsg(n)
            /\ UNCHANGED tasks
         \/ /\ Deactivate(n)
            /\ UNCHANGED tasks

------------------------------------------------------------------------------

(*  *)
SendTermination(n) ==
  /\ n = Initiator
  /\ active[Initiator] = FALSE
  /\ color[Initiator] = "white"
  \* Don't send termination message multiple times determined by looking at
  \* global state (an actual implementation obviously won't need this).
  /\ \A j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type # "trm"
  /\ \E j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type = "tok"
        /\ inbox[n][j].color = "white"
        /\ counter[Initiator] + inbox[n][j].q = 0
        \* Don't remove the token msg from inbox[Initiator]
        \* because it would mess up Inv, i.e. tpos.
\*        /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
  \* Send termination message to all nodes (including self).
  /\ inbox' = [ node \in Nodes |-> inbox[node] \o <<TrmMsg>>]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<tasks, active, color, counter>>                            

(* Override with Sys.exit *)
Terminate(n) == TRUE \*PrintT("sys.exit")

(*  *)
RecvTermination(n) ==
  /\ \E j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type = "trm"
  /\ Terminate(n)
  /\ UNCHANGED tvars

SysExit(n) ==  \/ SendTermination(n)
               \/ RecvTermination(n)

------------------------------------------------------------------------------

TInit == 
  /\ Init
  /\ tasks \in [Nodes -> 1..1]

TNext ==
  \/ /\ System
     /\ UNCHANGED tasks
  \/ Environment
  \/ \E n \in Nodes: SysExit(n)
  /\ UNCHANGED tasks

TSpec == TInit /\ [][TNext]_tvars /\ WF_vars(TNext)


TInv ==
  \/ Inv
  \* Sarfra's (inductive) invariant Inv is violated once the Initiator
  \* starts sending out termination messages.  We thus allow Inv to be
  \* violated from the point onwards that the Initiator initiated
  \* termination.
\*  \/ \E msg \in Range(inbox[Initiator]):
\*          msg.type = "trm"

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* not supposed to hold: any node may indefinitely perform local           *)
(* computations. However, this property is verified if the fairness        *)
(* condition WF_vars(Next) is used instead of only WF_vars(System) that    *)
(* requires fairness of the actions controlled by termination detection.   *)
(***************************************************************************)
SpecWFNext == Init /\ [][Next]_vars /\ WF_vars(Next)
AllNodesTerminateIfNoMessages ==
  <>[][\A i \in Nodes : ~ SendMsg(i)]_vars => <>(\A i \in Nodes : ~ active[i])

=============================================================================
