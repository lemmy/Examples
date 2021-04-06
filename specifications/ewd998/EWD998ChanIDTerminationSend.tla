-------------------- MODULE EWD998ChanIDTerminationSend --------------------
---------------------- MODULE EWD998ChanIDTermination ----------------------
(***************************************************************************)
(* This spec has the following two notable differences:                    *)
(*  - Add SendTermination and RecvTermination actions that model how the   *)
(*    Initiator notifies the ring about final termination                  *)
(*                                                                         *)
(*  - A constant operator Send(_) replaces the basic function operations   *)
(*    in anticipation of instantiation by refinements with Messaging.tla   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Naturals, Utils


CONSTANT Nodes
ASSUME IsFiniteSet(Nodes) /\ Nodes # {}

N == Cardinality(Nodes)

\* Choose a node to be the initiator of a fresh token. We don't care which one it
\* is as long as it is always the same.
Initiator == CHOOSE n \in Nodes : TRUE
                                         
\* Organize Nodes in a ring. 
RingOfNodes == 
  CHOOSE r \in [ Nodes -> Nodes ]: IsSimpleCycle(Nodes, r)

Color == {"white", "black"}

VARIABLES 
 active,
 color,
 counter,
 inbox
  
vars == <<active, color, counter, inbox>>

EWD998ChanID == INSTANCE EWD998ChanID

\* Define a new message type.
TrmMsg == [type |-> "trm"]
Message == EWD998ChanID!EWD998Chan!TokenMsg \cup EWD998ChanID!EWD998Chan!BasicMsg \cup TrmMsg

CONSTANT Send(_)

\* Assumes/Handles:
\* /\ \A p \in setOfPackets: Len(p) = 2 \* One message/payload per packet
\* /\ Cardinality(Senders) = Cardinality(setOfPackets) \* Maximum of one packet per Node/Sender
DirectSend(setOfPackets) ==
   LET Senders == { packet[1] : packet \in setOfPackets}
       Payload(sender) == LET packet(n) == CHOOSE packet \in setOfPackets : packet[1] = sender
                          IN packet(sender)[2] 
   IN inbox' = [ n \in Nodes |-> IF n \in Senders 
                                 THEN Append(inbox[n], Payload(n))
                                 ELSE inbox[n] ]
             
\* Poor mans re-define of TypeOK here because we sort of re-defined Message.
TypeOK ==
  /\ EWD998!TypeOK
  /\ inbox \in [Nodes -> Seq(Message)]

------------------------------------------------------------------------------
 
Init ==
  (* Rule 0 *)
  /\ counter = [n \in Nodes |-> 0] \* c properly initialized
  /\ inbox = [n \in Nodes |-> IF n = Initiator 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *) 
  /\ active \in [Nodes -> {TRUE}]
  /\ color \in [Nodes -> Color]

InitiateProbe ==
  (* Rule 1 *)
  /\ \E j \in 1..Len(inbox[Initiator]):
      \* Token is at node the Initiator.
      /\ inbox[Initiator][j].type = "tok"
      /\ \* Previous round inconsistent, if:
         \/ inbox[Initiator][j].color = "black"
         \/ color[Initiator] = "black"
         \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
         \* been achieved: Initiate a probe if the token's color is white but the
         \* number of in-flight messages is not zero.
         \/ counter[Initiator] + inbox[Initiator][j].q # 0
      /\ Send({<<RingOfNodes[Initiator], [type |-> "tok", q |-> 0, color |-> "white"]>>}) \* consume token message from inbox[0].
      /\ inbox' = [inbox EXCEPT ![Initiator] = RemoveAt(@, j) ]
  (* Rule 6 *)
  /\ color' = [ color EXCEPT ![Initiator] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            
  
PassToken(n) ==
  (* Rule 2 *)
  /\ ~ active[n] \* If machine i is active, keep the token.
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "tok"
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          /\ LET tkn == inbox[n][j]
             IN  /\ Send(<<RingOfNodes[n], [type |-> "tok",  
                                               q |-> tkn.q + counter[n],
                                                             color |-> IF color[n] = "black"
                                                                       THEN "black"
                                                                       ELSE tkn.color]>>)
                 /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ] \* pass on the token.
  (* Rule 7 *)
  /\ color' = [ color EXCEPT ![n] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            

System == \/ InitiateProbe
          \/ \E n \in Nodes \ {Initiator} : PassToken(n)

TSystem(n) ==
  IF n = Initiator
  THEN InitiateProbe
  ELSE PassToken(n)

-----------------------------------------------------------------------------

SendMsg(n) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[n]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Nodes \ {n} :
          \* Send a message (not the token) to j.
          /\ Send({<<j, [type |-> "pl" ]>>})
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color>>                            

\* RecvMsg could write the incoming message to a (Java) buffer from which the (Java) implementation consumes it. 
RecvMsg(n) ==
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![n] = "black" ]
  \* Receipt of a message activates node n.
  /\ active' = [ active EXCEPT ![n] = TRUE ]
  \* Consume a message (not the token!).
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "pl"
          /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
  /\ UNCHANGED <<>>                           

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E n \in Nodes : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

TEnvironment(n) ==
  \/ SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

-----------------------------------------------------------------------------

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
  /\ Send({ << m, [ type  |-> "trm", q |-> 0, color |-> "white" ]>> : m \in Nodes })
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, color, counter>>                            

(* Override with Sys.exit *)
Terminate(n) == TRUE \*PrintT("sys.exit")

(*  *)
RecvTermination(n) ==
  /\ \E j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type = "trm"
  /\ Terminate(n)
  /\ UNCHANGED vars

Termination(n) ==
  \/ SendTermination(n) 
  \/ RecvTermination(n)
  
------------------------------------------------------------------------------

\* We want the existential at the outermost level because of how PlusPy
\* maps the actual/physical nodes to the logical spec nodes.
TNext(n) ==
  \/ TSystem(n)
  \/ TEnvironment(n) 
  \/ Termination(n)

TSpec ==
  Init /\ [][\E n \in Nodes: TNext(n)]_vars
       \* Only relevant for safety-checking.
       /\ \A n \in Nodes:
           /\ WF_vars(TSystem(n))
           /\ WF_vars(TEnvironment(n))
           /\ WF_vars(Termination(n))

THEOREM TSpec => EWD998!Inv \* This is EWD998Chan!Inv all the way up.

THEOREM TSpec => EWD998!Spec
------------------------------------------------------------------------------

\* Iff termination is detected by EWD998, there are no payload messages
\* in any node's inbox.
InvA ==
  EWD998!EWD998!terminationDetected =>
        \A n \in Nodes: 
           \A msg \in Range(inbox[n]):
              msg.type # "pl"

\* Iff there is a termination message in any node's inbox, there are no
\* payload messages in any inbox.
InvB ==
  (\E n \in Nodes: 
    \E msg \in Range(inbox[n]): msg.type = "trm")
  =>
  (\A n2 \in Nodes:
    \A msg2 \in Range(inbox[n2]): msg2.type # "pl")

THEOREM TSpec => /\ InvB
                 /\ InvA

\* TerminationMessages does *not* hold because nodes can keep
\* sending (payload) messages indefinitely.
TerminationMessages ==
  <>[][\A n \in Nodes : RecvTermination(n)]_vars

\* Iff - from some point onward - none of the nodes send out
\* payload messages, all nodes will eventually terminate.
TerminationMessagesIfNoPayloadMessages ==
  <>[][\A n \in Nodes : ~ SendMsg(n)]_vars =>
               <>[][\A n \in Nodes : RecvTermination(n)]_vars

THEOREM TSpec => TerminationMessagesIfNoPayloadMessages
=============================================================================

TTypeOK ==
  /\ TypeOK!1
  /\ TypeOK!2
  /\ TypeOK!3
  \* Seq(Messages) fails because we can't subst EWD998ChanID!Message
  \* with TMessage above (to do that we'd have to refine EWD998ChanID).
\*  /\ TypeOK!4
  /\ inbox \in [Nodes -> Seq(TMessage)]
  /\ TypeOK!5
