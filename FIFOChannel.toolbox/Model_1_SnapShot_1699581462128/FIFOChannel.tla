--------------------------- MODULE FIFOChannel ---------------------------
EXTENDS Integers, Sequences, TLC

VARIABLE state, channel

(* Set of processes *)
Processes == 1..2

(* Initialize variables *)
Init == 
    /\ state = 0
    /\ channel = <<>>

(* Send a message from process i to process j *)
Send ==
    /\ channel' = Append(channel, 1)
    /\ UNCHANGED <<state>>

(* Receive a message by process j from process i *)
Receive ==
    /\ channel # <<>>
    /\ state' = state + Head(channel)
    /\ channel' = Tail(channel)

(* Next state of the system *)
Next == IF channel # <<>> 
            THEN Receive
            ELSE IF state < 10
                THEN Send
                ELSE UNCHANGED<<state, channel>> 
    
(* Temporal formula *)
Spec == Init /\ [][Next]_<<state, channel>>

=============================================================================
\* Modification History
\* Last modified Thu Nov 09 22:57:30 BRT 2023 by lucas
\* Last modified Fri Nov 03 09:10:05 BRT 2023 by gabif
\* Created Sun Oct 29 12:39:53 BRT 2023 by wagner.savaris