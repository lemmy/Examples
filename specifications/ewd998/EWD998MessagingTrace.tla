------------------------ MODULE EWD998MessagingTrace ------------------------
\*EXTENDS Naturals, Sequences, TLC

A == 0
B == 1
C == 2

Traces ==
<<
 [ 
  active |-> [ A |-> TRUE, B |-> TRUE, C |-> TRUE ]
 ]
>>

VARIABLES 
 active,
 color,
 counter,
 inbox,
 mi
 ,tasks
 
\*Model == INSTANCE EWD998Messaging

vars == <<tasks, active, color, counter, inbox, mi>>

\*Trace == Traces[log]
\*
\*Read == LET Rec == Trace[TLCGet("level") + 1] IN x = Rec.x /\ y = Rec.y /\ z = Rec.z /\ tickTock = Rec.tickTock
\*\*ReadNext == LET Rec == Trace[TLCGet("level") + 1] IN x' = Rec[1] /\ y' = Rec[2] /\ z' = Rec[3] /\ tickTock' = Rec[4]
\*
\*ReadNext(v, l) == x' = Traces[l].x /\ y' = Traces[l].y /\ z' = Traces[l].z /\ tickTock = Traces[l].tickTock
\*
\*Init == PrintT(TLCGet("diameter")) /\ log \in DOMAIN Traces /\ Read
\*
\*Next == /\ \/ TLCGet("level") + 1 <= Len(Trace) /\ x' = ReadNext("x", TLCGet("level"))
\*           \/ UNCHANGED <<log, vars>>
\*        /\ UNCHANGED <<log>>
\*
\*TraceBehavior == Init /\ [][Next]_<<log, vars>>

\*THEOREM TraceBehavior => Model!Safety


=============================================================================
