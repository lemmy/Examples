------------------- MODULE EWD998ChanIDTerminationBackup -------------------

THEOREM Spec => EWD998!Inv \* This is EWD998Chan!Inv all the way up.

THEOREM Spec => EWD998!Spec
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
=============================================================================

------------------------------------------------------------------------------

TTypeOK ==
  /\ TypeOK!1
  /\ TypeOK!2
  /\ TypeOK!3
  \* Seq(Messages) fails because we can't subst EWD998ChanID!Message
  \* with TMessage above (to do that we'd have to refine EWD998ChanID).
\*  /\ TypeOK!4
  /\ inbox \in [Nodes -> Seq(TMessage)]
  /\ TypeOK!5


=============================================================================
