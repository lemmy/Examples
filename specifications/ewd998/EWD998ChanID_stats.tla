---------------------------- MODULE EWD998ChanID_stats ----------------------------
EXTENDS EWD998ChanID, CSV

CSVFile ==
    "EWD998ChanID_" \o ToString(JavaTime) \o ".csv"

ASSUME 
    CSVWrite("Variant#Node#Length#T#T2TD#InitiateProbe#PassToken#SendMsg#RecvMsg#Deactivate",
             <<>>, CSVFile)

ASSUME TLCGet("config").mode = "generate"
\* Do not artificially restrict the length of behaviors.
ASSUME TLCGet("config").depth = -1
\* The algorithm terminates. Thus, do not check for deadlocks.
ASSUME TLCGet("config").deadlock = FALSE
\* Require a recent versions of TLC with support for the operators appearing below.
ASSUME TLCGet("revision").timestamp >= 1663391404

AtTerminationDetected ==
    \* Cfg: CONSTRAINT AtTerminationDetected
    terminationDetected =>
          \* Append record to CSV file on disk.
          /\ CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s#%8$s#%9$s#%10$s",
               << feature, N, TLCGet("level"), -1, passes, -1,-1,-1,-1,-1 >>,
               CSVFile)

=============================================================================
