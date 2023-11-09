--------------------------- MODULE FIFOChannel ---------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT NumProcesses

VARIABLE state, channels

(* Set of processes *)
Processes == 1..NumProcesses

(* Initialize variables *)
Init == 
    /\ state = [i \in Processes |-> <<>>]
    /\ channels = [i, j \in Processes |-> <<>>]

(* Send a message from process i to process j *)
Send(i, j, msg) == 
    /\ channels' = [channels EXCEPT ![i, j] = Append(channels[i, j], msg)]
    /\ UNCHANGED <<state>>

(* Receive a message by process j from process i *)
Receive(i, j) ==
    /\ channels[i, j] # <<>>
    /\ state' = [state EXCEPT ![j] = Append(state[j], Head(channels[i, j]))]
    /\ channels' = [channels EXCEPT ![i, j] = Tail(channels[i, j])]

(* Next state of the system *)
Next ==
    \/ \E i, j \in Processes: Send(i, j, "Message from " \o ToString(i) \o " to " \o ToString(j))
    \/ \E i, j \in Processes: Receive(i, j)

(* Temporal formula *)
Spec == Init /\ [][Next]_<<state, channels>>

=============================================================================
\* Modification History
\* Last modified Thu Nov 09 17:40:10 BRT 2023 by lucas
\* Last modified Fri Nov 03 09:10:05 BRT 2023 by gabif
\* Created Sun Oct 29 12:39:53 BRT 2023 by wagner.savaris