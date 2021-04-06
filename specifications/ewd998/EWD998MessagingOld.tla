------------------------- MODULE EWD998MessagingOld -------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* Contrary to EWD998, this variant models message channels as sequences.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC\*, Bags


------------------------------------------------------------------------------

\* What's the correct mathmatical term for this?  Can probably be stated as
\* properties that do not require recursive computation.
\*RECURSIVE Closure(_,_,_,_)  \* No support for RECURSIVE in PlusPy.
\*Closure(fnc, elem, steps, collected) == 
\*  IF steps = 0
\*  THEN collected
\*  ELSE Closure(fnc, fnc[elem], steps - 1, collected \cup {fnc[elem]})

IsSimpleCycle(S, r) ==
  (* View r as a graph s.t. S is the graph's set of vertices and there 
     exists an edge from s to t iff f[s] = t. IsFiniteSet(DOMAIN r). *)
  LET 
   Range(f) == { f[x] : x \in DOMAIN f }
      F[ i \in 1..Cardinality(S) ] == 
         IF i = 1 THEN << CHOOSE s \in S : TRUE >>
         ELSE LET seq == F[i-1]
                  head == Head(seq)
              IN << r[head] >> \o F[i-1]
  IN Range(F[Cardinality(S)]) = S
         
------------------------------------------------------------------------------

\*CONSTANT Processes \* PlusPy uses refinement in place of a TLC model. 
Nodes == { "localhost:5001", "localhost:5002", "localhost:5003" }
\*Nodes == {"A","B","C"}
ASSUME IsFiniteSet(Nodes)

N == Cardinality(Nodes)

\* Choose a node to be the initiator of a fresh token. We don't care which one it
\* is as long as it is always the same.
Initiator == CHOOSE n \in Nodes : TRUE
                                         
\* Bring Processes/Nodes into some order to define a ring of nodes. 
RingOfNodes == 
  CHOOSE r \in [ Nodes -> Nodes ]: IsSimpleCycle(Nodes, r)

Color == {"white", "black"}

Q == Int
ASSUME 0 \in Q

VARIABLES 
 active, color, counter, \* EWD998
 inbox, tasks,           \* Auxiliary variables
 mi                      \* Messaging
  
vars == <<tasks, active, color, counter, inbox, mi>>

\* This is a hack to make it work with Messaging.tla which supports
\* only a single type of messages.
TokenMsg == [type : {"tok", "pl", "trm"}, q : Q, color : Color]
\*BasicMsg == [type : {"pl"}]
Message == TokenMsg \* \cup BasicMsg

Network == INSTANCE Messaging WITH Processes <- Nodes

TypeOK ==
  /\ counter \in [Nodes -> Int]
  /\ active \in [Nodes -> {TRUE, FALSE}] \* PlusPy doesn't parse BOOLEAN.
  /\ color \in [Nodes -> Color]
  /\ inbox \in [Nodes -> Seq(Message)]
  \* There is always exactly one token (singleton-type).
\*  /\ \E i \in Nodes : \E j \in 1..Len(inbox[i]): inbox[i][j].type = "tok"
\*  /\ \A i,j \in Nodes : \A k \in 1 .. Len(inbox[i]) : \A l \in 1 .. Len(inbox[j]) :
\*        inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok"
\*        => i = j /\ k = l

------------------------------------------------------------------------------
 
Init ==
  (* Rule 0 *)
  /\ counter = [i \in Nodes |-> 0] \* c properly initialized
  /\ inbox = [ [i \in Nodes |-> {}]  \* with empty channels except a token at inbox[0].
                EXCEPT ![Initiator] = 
                     {[type  |-> "tok", q |-> 0, color |-> "black"]} ]
  (* EWD840 *) 
  /\ active \in [Nodes -> {TRUE}] \* PlusPy doesn't parse BOOLEAN.
                                  \* With PlusPy, we probably want to redefine Init
                                  \* s.t. at least one Node is active.
  /\ color \in [Nodes -> (Color \ {"white"})] \* Determinisitc initial state.
  (* Networking *)
  /\ Network!Init
  /\ tasks \in [Nodes -> 1..1]

\* This is never enabled because we don't initialize the inbox[0] with a token--as a matter of fact, there is no token in the system right now.
InitiateProbe(n) ==
  /\ n = Initiator
  /\ ~ \E msg \in inbox[n]: msg.type = "pl"  
  (* Rule 1 *)
  /\ \E msg \in inbox[n]:
        \* Token is at node 0.
        /\ msg.type = "tok"
        /\ \* Previous round inconsistent, if:
           \/ msg.color = "black"
           \/ color[n] = "black"
           \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
           \* been achieved: Initiate a probe if the token's color is white but the
           \* number of in-flight messages is not zero.
           \/ counter[n] + msg.q # 0
        \* consume token message from inbox[0].
        /\ inbox' = [inbox EXCEPT![n] = @ \ {msg} ]
  /\ Network!Send({ << RingOfNodes[n], [ type  |-> "tok", 
                                             q |-> 0,
                                              (* Rule 6 *)
                                         color |-> "white" ]>> })
  (* Rule 6 *)
  /\ color' = [ color EXCEPT ![n] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<tasks, active, counter>>                            
  
PassToken(n) ==
  (* Rule 2 *)
  /\ ~ active[n] \* If machine i is active, keep the token.
  /\ ~ \E msg \in inbox[n]: msg.type = "pl"  
  /\ \E msg \in inbox[n] : 
          /\ msg.type = "tok"
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          /\ Network!Send({ << RingOfNodes[n],  [msg EXCEPT 
                                                     !.q = msg.q + counter[n],
                                                     !.color = IF color[n] = "black"
                                                               THEN "black"
                                                               ELSE msg.color]>> })
          \* Pass on the token (no longer ours).
          /\ inbox' = [inbox EXCEPT![n] = @ \ {msg} ]
  (* Rule 7 *)
  /\ color' = [ color EXCEPT ![n] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<tasks, active, counter>>                            

System(n) == \/ /\ n = Initiator 
                /\ InitiateProbe(n)
             \/ /\ n # Initiator
                /\ PassToken(n)

-----------------------------------------------------------------------------

SendMsg(n) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[n]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  \* Explicitly model a finite number of messages.
  /\ tasks[n] > 0
  /\ tasks' = [tasks EXCEPT ![n] = @ - 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Nodes \ {n} :
          \* Send a message (not the token) to j.
          /\ Network!Send({ << j, [type |-> "pl", q |-> 0, color |-> "black" ]>> }) \* This is a hack to make it work with Messaging.tla
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color, inbox>>                            

\* RecvMsg could write the incoming message to a (Java) buffer from which the (Java) implementation consumes it. 
RecvMsg(n) ==
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![n] = "black" ]
  \* Receipt of a message activates i.
  /\ active' = [ active EXCEPT ![n] = TRUE ]
  \* Consume a message (not the token!).
  /\ \E msg \in inbox[n] : 
          /\ msg.type = "pl"
          /\ inbox' = [inbox EXCEPT ![n] = @ \ {msg} ]
\*  /\ PrintT("######\n$$$$$$ Executing some heavy computation...\n######")
  /\ UNCHANGED <<tasks, mi>>                           

Deactivate(n) ==
  /\ active[n]
  /\ tasks[n] = 0
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<tasks, color, inbox, counter, mi>>

Environment(n) == \/ SendMsg(n)
                  \/ RecvMsg(n)
                  \/ Deactivate(n)

-----------------------------------------------------------------------------

SendTermination(n) ==
  /\ n = Initiator
  /\ active[Initiator] = FALSE
  /\ color[Initiator] = "white"
  /\ \E msg \in inbox[Initiator]:
        \* Token is at the Initiator node.
        /\ msg.type = "tok"
        /\ msg.color = "white"
        /\ counter[Initiator] + msg.q = 0
        /\ inbox' = [inbox EXCEPT ![Initiator] = @ \ {msg} ]
  /\ Network!Send({ << m, [ type  |-> "trm", q |-> 0, color |-> "white" ]>> : m \in Nodes })
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<tasks, active, color, counter>>                            

\* TODO: Add action that --upon receiving a termination message-- goes to "Done".
\* In PlusPy, this will be overriden with a call to sys.exit.  InitiateProbe also
\* has to be amended to send a termination message.
Terminate(n) == TRUE \*PrintT("sys.exit") \* Override with Sys.exit

RecvTermination(n) ==
  /\ \E msg \in inbox[n] : 
         /\ msg.type = "trm"
\*         /\ inbox' = [inbox EXCEPT ![n] = @ \ {msg} ]
  /\ Terminate(n)
  /\ UNCHANGED <<tasks, active, color, counter, inbox, mi>> 

SysExit(n) ==  \/ SendTermination(n)
               \/ RecvTermination(n)

-----------------------------------------------------------------------------

\* Deliver messages from the network layer to a nodes' inbox (either payload or token).
\*TODO Merge Deliver and RecvMsg for payload messages and Deliver and PassToken
\* for the token.
Deliver(n, msg) ==
  /\ inbox' = [ inbox EXCEPT ![n] = @ \union { msg } ]
  /\ UNCHANGED <<tasks, active, counter, color>>

-----------------------------------------------------------------------------

\* PlusPy will call Proc and not next to map a real-world machine to n.
Proc(n) == 
   \/ System(n)
   \/ Environment(n)
   \/ SysExit(n)
   \/ Network!Receive(n, Deliver)

Next ==
  \E n \in Nodes : Proc(n)
  
=============================================================================
   
   + Model node identities with addresses instead of natural numbers
   + Send/Receive termination messages
   ---
   + Proc(n) because we need a way to pass in the node's id (PlusPy)
   ---
   * Use PlusPy Delivery approach
   * Fix PlusPy to handle multiple messages to get rid of message hack.
   
   
Spec == Init /\ [][Next]_vars 
             /\ WF_vars(Next) \* Not parsed by PlusPy yet.

-----------------------------------------------------------------------------
chan == INSTANCE EWD998Chan

(***************************************************************************)
(* The number of incoming messages of a node's given inbox.                *)
(***************************************************************************)
NumberOfMsg(ibx) == 
  Len(SelectSeq(ibx, LAMBDA msg: msg.type = "pl"))

\*Range(f) == { f[x] : x \in DOMAIN f }

SeqOf(set, n) ==
  UNION {[1..m -> set] : m \in 0..n}

i2n == CHOOSE seq \in SeqOf(Nodes, N) : Range(seq) = Nodes
      
(***************************************************************************)
(* The number of messages on their way. "in-flight"                        *)
(* Contrary to reasoning about the local counter below, this reasoning     *)
(* requires a global view of the world (all channels/inboxes.              *)
(***************************************************************************)
B == 
  LET F[ i \in 1..N ] == 
         IF i = 1 THEN NumberOfMsg(inbox[i2n[i]])
         ELSE NumberOfMsg(inbox[i2n[i]]) + F[i-1]
  IN F[N]

(***************************************************************************)
(* Safra's inductive invariant                                             *)
(***************************************************************************)
Inv == 
  /\ P0:: B = LET F[ i \in 1..N ] == 
                     IF i = 1 THEN counter[i2n[i]]
                     ELSE counter[i2n[i]] + F[i-1]
              IN F[N]

  
AllTerminate ==
  <>[]\A n \in Nodes: inbox[n] = { [type|->"trm", q|->0, color|->"white"] }
=============================================================================
