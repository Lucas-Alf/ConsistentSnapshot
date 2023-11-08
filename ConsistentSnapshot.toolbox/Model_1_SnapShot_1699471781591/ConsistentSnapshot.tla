--------------------------- MODULE ConsistentSnapshot ---------------------------
EXTENDS Naturals, Sequences

CONSTANT NumProcesses

(* Constantes *)
Processes == 1..NumProcesses    \* Número de processos
Channels == NumProcesses * 2    \* Número de canais
InitState == [p \in Processes |-> "active"]  \* Estado inicial de todos os processos

(* Variáveis *)
VARIABLES
  state,       \* Estado atual de cada processo
  snapshot,    \* Snapshot coletado
  messages     \* Mensagens recebidas por cada processo

(* Inicialização *)
Init ==
  /\ state = InitState
  /\ snapshot = [p \in Processes |-> ""]
  /\ messages = [p1 \in Processes, p2 \in Processes, c \in Channels |-> <<>>]


(* Funções Auxiliares *)
UpdateState(p, novoEstado) == 
  /\ state' = [state EXCEPT ![p] = novoEstado]
  /\ UNCHANGED <<snapshot, messages>>

Send(p1, p2, c, msg) ==
  /\ messages' = [messages EXCEPT ![p1, p2, c] = Append(messages[p1, p2, c], msg)]
  /\ UNCHANGED <<state, snapshot>>

Receive(p1, p2, c) ==
  /\ LET msgs == Head(messages[p1, p2, c])
     IN
       /\ IF Len(messages[p1, p2, c]) > 1 
          THEN
             /\ messages' = [messages EXCEPT ![p1, p2, c] = Tail(messages[p1, p2, c])]
             /\ UNCHANGED <<state, snapshot>>
             /\ msgs
          ELSE
             /\ messages' = [messages EXCEPT ![p1, p2, c] = <<>>]
             /\ UNCHANGED <<state, snapshot>>
             /\ msgs

(* Comportamento de Transição *)
Next ==
  \* Regras para a transição de estados
  /\ \A p \in Processes :
      \/ /\ state[p] = "active"
          /\ \E q \in Processes :
              /\ q # p
              /\ \E c \in Channels :
                  /\ Send(p, q, c, "snapshot")
                  /\ \E msg \in BOOLEAN :
                      /\ Receive(q, p, c) = msg
                      /\ IF msg THEN UpdateState(p, "running") ELSE TRUE
              /\ IF \A x \in Processes : state[x] = "running"
                 THEN UpdateState(p, "terminated")
                 ELSE UpdateState(p, "active")
                 
      \/ /\ state[p] = "running"
          /\ \E c \in Channels :
              /\ \E msg \in BOOLEAN :
                  /\ Receive(p, p, c) = msg
                  /\ IF msg THEN UpdateState(p, "terminated") ELSE TRUE

      \/ /\ state[p] = "terminated"
          /\ UNCHANGED <<state, snapshot, messages>>

(* Comportamento Específico *)
Spec ==
  /\ \A p \in Processes : state[p] = "terminated"
  /\ \A p \in Processes :
      /\ snapshot[p] = state[p]
      /\ \A q \in Processes :
          /\ q # p => snapshot[q] = ""
          
=============================================================================
\* Modification History
\* Last modified Wed Nov 08 16:06:33 BRT 2023 by lucas
\* Last modified Fri Nov 03 09:10:05 BRT 2023 by gabif
\* Created Sun Oct 29 12:39:53 BRT 2023 by wagner.savaris