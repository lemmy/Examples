-------------------------- MODULE EWD998ChanIDOld --------------------------
\* No support for RECURSIVE in PlusPy.  Leaving here for reference.
\*RECURSIVE IsSimpleCycle(_,_,_,_)
\*IsSimpleCycle(fnc, elem, steps, collected) == 
\*  IF steps = 0
\*  THEN collected
\*  ELSE IsSimpleCycle(fnc, fnc[elem], steps - 1, collected \cup {fnc[elem]})
IsSimpleCycle(S, r) ==
  (* View r as a graph s.t. S is the graph's set of vertices and there 
     exists an edge from s to t iff f[s] = t. IsFiniteSet(DOMAIN r). *)
  LET 
   Range(f) ==  { f[x] : x \in DOMAIN f }
   F[ i \in 1..Cardinality(S) ] == 
         IF i = 1 THEN << CHOOSE s \in S : TRUE >>
         ELSE LET seq == F[i-1]
                  head == Head(seq)
              IN << r[head] >> \o F[i-1]
  IN Range(F[Cardinality(S)]) = S
         


\*-----------------------------------------------------------------------------
\*
\* 0..N-1 where Initiator has position 0 and its successor has position N-1.
\*Position(node) ==
\*   LET RECURSIVE Op(_,_,_)
\*       Op(nd, cur, pos) == 
\*          IF nd = cur THEN pos
\*          ELSE Op(nd, RingOfNodes[cur], pos - 1)
\*   IN Op(node, RingOfNodes[Initiator], N-1)
\*  
\*Node2Position ==
\*  [ n \in Nodes |-> Position(n) ]
\*
\*(***************************************************************************)
\*(* The number of incoming messages of a node's given inbox.                *)
\*(***************************************************************************)
\*NumberOfMsg(ibx) == 
\*  Len(SelectSeq(ibx, LAMBDA msg: msg.type # "tok"))
\*
\*(***************************************************************************)
\*(* Bound the otherwise infinite state space that TLC has to check.         *)
\*(***************************************************************************)
\*StateConstraint ==
\*  /\ \A i \in DOMAIN inbox : NumberOfMsg(inbox[i]) < 3
\*\*  /\ \A i \in DOMAIN inbox : Len(inbox[i]) < 3
\*  \* Even with the number of in-flight messages restricted, we need a bound
\*  \* on the number of messages ever sent to exclude behaviors where two or
\*  \* more nodes forever alternate between send, receive, send, ...
\*  /\ \A i \in DOMAIN counter : counter[i] < 3
\*
\*-----------------------------------------------------------------------------
\*
\*(***************************************************************************)
\*(* tpos \in Nodes s.t. the node's inbox contains the token.                *)
\*(***************************************************************************)
\*tpos ==
\*  CHOOSE n \in Nodes : \E j \in 1..Len(inbox[n]) : inbox[n][j].type = "tok"
\* 
\*(***************************************************************************)
\*(* The q value of the token.                                               *) 
\*(***************************************************************************)
\*tq ==
\*  LET box == CHOOSE i \in 1..Len(inbox[tpos]) : inbox[tpos][i].type = "tok"
\*  IN inbox[tpos][box].q
\*\* TLC doesn't evaluate n \in Int unless Int replaced with a def override.
\*\*  CHOOSE n \in Int : 
\*\*            \E i \in Nodes : 
\*\*             \E j \in 1..Len(inbox[i]) : 
\*\*              /\ inbox[i][j].type = "tok"
\*\*              /\ inbox[i][j].q = n                                          
\*
\*(***************************************************************************)
\*(* Main safety property: if there is a white token at node 0 and there are *)
\*(* no in-flight messages then every node is inactive.                      *)
\*(***************************************************************************)
\*terminationDetected ==
\*  /\ tpos = 0 \* Redundant because of msg.type = "tok" below.
\*  /\ \E j \in 1..Len(inbox[0]) : /\ inbox[0][j].type = "tok"
\*                                 /\ inbox[0][j].color = "white"
\*                                 \* no messages in-flight.
\*                                 /\ inbox[0][j].q + counter[0] = 0
\*  /\ color[0] = "white"
\*  /\ ~ active[0]
\*
\*(***************************************************************************)
\*(* The number of messages on their way. "in-flight"                        *)
\*(* Contrary to reasoning about the local counter below, this reasoning     *)
\*(* requires a global view of the world (all channels/inboxes).             *)
\*(***************************************************************************)
\*B == 
\*  LET RECURSIVE sum(_)
\*      sum(nodes) == IF nodes = {} THEN 0
\*                    ELSE LET n == CHOOSE n \in nodes : TRUE
\*                            IN sum(nodes \ {n}) + NumberOfMsg(inbox[n])
\*  IN sum(Nodes)
\*
\*(***************************************************************************)
\*(***************************************************************************)
\*TerminationDetection ==
\*  terminationDetected => /\ \A i \in Nodes : ~ active[i]
\*                         /\ B = 0 \* No messages in-flight.
\*
\*RECURSIVE sumFcn(_,_)
\*sumFcn(fcn, set) == IF set = {} THEN 0
\*                    ELSE LET s == CHOOSE s \in set : TRUE
\*                         IN sumFcn(fcn, set \ {s}) + fcn[s]
\*
\*\* For Inv below it is convenient to be able to get the set of nodes that
\*\* are a sub-path/sub-sequence on ring of nodes.  Note that the ring is a
\*\* directed graph!!! If you want to inverse direction, the complement 
\*\* DOMAIN RingOfNodes \ path(from,to) should do it.
\*RECURSIVE path(_,_)
\*path(from, to) ==
\*  IF from = to THEN <<from>>
\*  ELSE <<from>> \o path(RingOfNodes[from], to)
\*  
\*\* <<RingOfNodes,  "B" ... "B", "B" ... "D", "D" ... "B", "C"..."A">>
\*from ... to ==
\*  path(from, to)
\*
\*\* The set of nodes on the path tpos+1 to N-1. Semantically, it's those
\*\* nodes that have send a token in this round (the Initiator is by def
\*\* not in this set).
\*S == Range(Initiator...tpos) \ {tpos, Initiator}
\*
\*\* The set of nodes on the path 0 to tpos.  The nodes that haven't seen
\*\* the token (for this round) yet.
\*R == Range(tpos...Initiator)
\*
\*(***************************************************************************)
\*(* Safra's inductive invariant                                             *)
\*(***************************************************************************)
\*IInv == 
\*  /\ P0:: B = sumFcn(counter, Nodes)
\*     (* (Ai: t < i < N: machine nr.i is passive) /\ *)
\*     (* (Si: t < i < N: ci.i) = q *)
\*  /\ 
\*     \/ P1:: /\ \A i \in S: ~ active[i] \* machine nr.i is passive
\*             /\ sumFcn(counter, S) = tq
\*     (* (Si: 0 <= i <= t: c.i) + q > 0. *)
\*     \/ P2:: sumFcn(counter, R) + tq > 0
\*     (* Ei: 0 <= i <= t : machine nr.i is black. *)
\*     \/ P3:: \E i \in R : color[i] = "black"
\*     (* The token is black. *)
\*     \/ P4:: \E i \in DOMAIN inbox:
\*              \E j \in 1..Len(inbox[i]): /\ inbox[i][j].type = "tok"
\*                                         /\ inbox[i][j].color = "black"
\*
\*(***************************************************************************)
\*(* Liveness property: termination is eventually detected.                  *)
\*(***************************************************************************)
\*Liveness ==
\*  (\A i \in Nodes : ~ active[i] /\ B = 0) ~> terminationDetected
\*

=============================================================================
\* Modification History
\* Last modified Wed May 27 14:41:22 PDT 2020 by markus
\* Created Wed May 27 14:40:24 PDT 2020 by markus
