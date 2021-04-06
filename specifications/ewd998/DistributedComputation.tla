.----------------------- MODULE DistributedComputation -----------------------
EXTENDS Naturals

\* Better refactored into constants, but PlusPy doesn't
\* support TLC models.
Nodes == {"n1","n2", "n3"}

Initiator == CHOOSE n \in Nodes : TRUE

CONSTANT Messages

VARIABLES 
   active,
   color,
   counter,
   inbox,
   stage
vars == 
  <<active, color, counter, inbox, stage>>

\* Why don't we use Stephan's Echo (Spanning Tree) spec as an example?
\* The initiator node of Echo knows when the algorithm has terminated.
\* Thus, there is no need to detect termination with EWD998, because
\* the initiator can immediately send a shutdown message.
\*
\* We cannot re-use EWD998's token message as a global timer because
\* a node keeps the token as long as it is active.  Only when the node
\* has become inactive does it pass the token to its successor (in the
\* ring). 
\*CD == INSTANCE Computation

TD == INSTANCE EWD998ChanID

SD == INSTANCE Shutdown

\* Messages defined to equal AllMessages in TLC model.  Doesn't work
\* if coverage/profiling is turned on due to bug Github #471 (see
\* https://github.com/tlaplus/tlaplus/issues/471).
AllMessages == 
  TD!EWD998Chan!Message \cup {SD!TrmMsg}

\* Assume of Messages has to come after instantiating EWD998ChanID.
\* TLC fails to evaluate it because the q component of TokenMsg is
\* Int, thus axiom not assumption (better, use model override).
AXIOM AllMessages = Messages
       
Init ==
  /\ stage = "A"
  /\ TD!Init 
  /\ SD!Init
  
Next(n) ==
  \/ /\ stage = "A"
     /\ [TD!Next(n)]_vars
     /\ UNCHANGED stage
  \/ \* The TD spec stutters forever after EWD998 has detected
     \* termination.  This is when we transition from stage A
     \* to stage B in spec DistributedComputation and commence
     \* an orderly shutdown via spec SD.  I don't expect this
     \* work with PlusPy though (To get rid of ENABLED here,
     \* the workaround would be to refactor the stage variable
     \* into spec TD and SD).
     /\ ~ ENABLED TD!Next(n)
     /\ stage = "A"
     /\ stage' = "B"
     /\ UNCHANGED <<active, color, counter, inbox>>
  \/ \* Orderly shutdown via spec SD.
     /\ stage = "B"
     /\ [SD!Next(n)]_vars
     /\ UNCHANGED <<active, color, counter, stage>>
  
Spec == 
  /\ Init
  /\ [][\E n \in Nodes: Next(n)]_vars  
  
=============================================================================
