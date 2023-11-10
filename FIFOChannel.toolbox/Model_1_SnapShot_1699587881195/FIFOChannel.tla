--------------------------- MODULE FIFOChannel ---------------------------
EXTENDS Integers, Sequences, TLC

VARIABLE state, channel

vars == <<state, channel>>

(* Set of processes *)
Processes == 0..1

(* Initialize variables *)
Init == 
    /\ state = [p \in Processes |-> 0]
    /\ channel = [p \in Processes |-> <<>>]

(* Send a message from process i to process j *)
Send(p) ==
    /\ PrintT("send")
    /\ channel' = [channel EXCEPT ![p] = Append(channel[p], 1)]
    /\ PrintT(channel')
    /\ UNCHANGED <<state>>

(* Receive a message by process j from process i *)
Receive(p) ==
    /\ PrintT("receive")
    /\ PrintT(channel[p])
    /\ channel[p] # <<>>
    /\ state' =   [state EXCEPT ![p] = state[p] + Head(channel[p])]
    /\ channel' = [channel EXCEPT ![p] = Tail(channel[p])]

(* Next state of the system *)
Next == \A p \in Processes :
    IF channel[p] # <<>> 
        THEN Receive(p)
    ELSE IF state[p] < 10
         THEN Send(p)
         ELSE FALSE
        
(* Fairness constraints *)
FairSend == \A p \in Processes : WF_vars(Send(p))
FairReceive == \A p \in Processes : WF_vars(Receive(p))

(* Temporal formula *)
Spec == Init /\ [][Next]_vars /\ FairSend /\ FairReceive
=============================================================================
\* Modification History
\* Last modified Fri Nov 10 00:44:25 BRT 2023 by lucas
\* Last modified Fri Nov 03 09:10:05 BRT 2023 by gabif
\* Created Sun Oct 29 12:39:53 BRT 2023 by wagner.savaris