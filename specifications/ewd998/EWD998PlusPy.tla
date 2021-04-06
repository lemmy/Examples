---------------------------- MODULE EWD998PlusPy ----------------------------
EXTENDS FiniteSets \*EWD998ChanIDTermination

PPNodes == { "localhost:5001", "localhost:5002", "localhost:5003" }
\*Nodes == {"A","B","C"}
ASSUME IsFiniteSet(PPNodes)

VARIABLES 
 active,
 color,
 counter,
 inbox,
 mi                      \* Messaging/Network

Network == INSTANCE Messaging WITH Processes <- PPNodes,
                                   Message <- TRUE
                                   
EWD998 == INSTANCE EWD998ChanIDTermination WITH Nodes <- PPNodes                                   
                                   

Deliver(n, msg) ==
  /\ inbox' = [ inbox EXCEPT ![n] = @ \union { msg } ]
  /\ UNCHANGED <<active, counter, color>>

------------------------------------------------------------------------------
  
TNext(n) ==
  \/ EWD998!TSystem(n)
  \/ EWD998!TEnvironment(n) 
  \/ EWD998!Termination(n)

=============================================================================
\* Modification History
\* Last modified Thu May 28 15:39:50 PDT 2020 by markus
\* Created Thu May 28 15:07:45 PDT 2020 by markus
