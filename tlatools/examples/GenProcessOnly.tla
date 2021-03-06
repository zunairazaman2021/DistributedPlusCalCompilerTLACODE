--------------------------- MODULE GenProcessOnly ---------------------------
EXTENDS TLC, Naturals, Integers, Sequences
CONSTANT P, Q
ASSUME P \in Nat
Processes == 1..P
ProcessesQ == P+1..Q
SubNodes == 4..5

(* PlusCal options (-termination  -distpcal) *)

(*--algorithm Syntax
variables x = 0;
fifos network[Processes, Processes];
fair+ process p \in Processes
begin
     A: x := x+1 ;
     ExA: x := 1 ;
end process
begin
     N: x := x+1 ;
     NX: x := 0;
end subprocess
begin
 replicate i \in 4..5;
     BX: x := x+1 ;
end subprocess

fair process q \in ProcessesQ
begin
     D: x := x+1 ;
     ExD: x := x+1;
end process
begin 
    E: x := x+1;
    EXTRA: x := x+1;
end subprocess
begin 
 replicate q \in SubNodes;
    F: x := x+1;
end subprocess
begin 
    replicate i \in SubNodes;
    G: x := x+1;
end subprocess
end algorithm;
*)

\* BEGIN TRANSLATION (chksum(pcal) = "bb043434" /\ chksum(tla) = "cc8f18c8")
VARIABLES x, network, pc

vars == << x, network, pc >>

ProcSet == (Processes) \cup (ProcessesQ)

Genprocs1 == { <<p>>: p \in Processes }

Genprocs1Thread1 == { <<p,1>>: p \in Processes }

Genprocs1Thread2 == { <<p,2,i>>: p \in Processes, i \in 4..5}

Genprocs2 == { <<p>>: p \in ProcessesQ }

Genprocs2Thread1 == { <<p,1>>: p \in ProcessesQ }

Genprocs2Thread2 == { <<p,2,q>>: p \in ProcessesQ, q \in SubNodes}

Genprocs2Thread3 == { <<p,3,i>>: p \in ProcessesQ, i \in SubNodes}

Init == (* Global variables *)
        /\ x = 0
        /\ network = [_n10 \in Processes, _n21 \in Processes |-> <<>>]
        /\ pc = [self \in Genprocs1 \union Genprocs1Thread1 \union Genprocs1Thread2 \union Genprocs2 \union Genprocs2Thread1 \union Genprocs2Thread2 \union Genprocs2Thread3 |-> CASE  self \in Genprocs1 -> "A"
		 [] self \in Genprocs1Thread1 -> "N"
		 [] self \in Genprocs1Thread2 -> "BX"
		 [] self \in Genprocs2 -> "D"
		 [] self \in Genprocs2Thread1 -> "E"
		 [] self \in Genprocs2Thread2 -> "F"
		 [] self \in Genprocs2Thread3 -> "G" ]

A(self) == /\ pc[<<self >>] = "A"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self>>] = "ExA"]
           /\ UNCHANGED network

ExA(self) == /\ pc[<<self >>] = "ExA"
             /\ x' = 1
             /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
             /\ UNCHANGED network

N(self) == /\ pc[<<self , 1>>] = "N"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "NX"]
           /\ UNCHANGED network

NX(self) == /\ pc[<<self , 1>>] = "NX"
            /\ x' = 0
            /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
            /\ UNCHANGED network

BX(self,i) == /\ pc[<<self , 2, i>>] = "BX"
              /\ x' = x+1
              /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]
              /\ UNCHANGED network

p(self) == A(self) \/ ExA(self)

psub1(self)  == N(self) \/ NX(self)

pi1replicate(self, i)  == BX(self, i)


D(self) == /\ pc[<<self >>] = "D"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self>>] = "ExD"]
           /\ UNCHANGED network

ExD(self) == /\ pc[<<self >>] = "ExD"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
             /\ UNCHANGED network

E(self) == /\ pc[<<self , 1>>] = "E"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "EXTRA"]
           /\ UNCHANGED network

EXTRA(self) == /\ pc[<<self , 1>>] = "EXTRA"
               /\ x' = x+1
               /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
               /\ UNCHANGED network

F(self,i) == /\ pc[<<self , 2, i>>] = "F"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]
             /\ UNCHANGED network

G(self,i) == /\ pc[<<self , 3, i>>] = "G"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self, 3, i>>] = "Done"]
             /\ UNCHANGED network

q(self) == D(self) \/ ExD(self)

qsub1(self)  == E(self) \/ EXTRA(self)

qq1replicate(self, i)  == F(self, i)

qi2replicate(self, i)  == G(self, i)


Next ==    \/ (\E self \in Processes: p(self))
           \/ \E self \in Processes: psub1(self)
           \/ \E self \in Processes, i \in 4..5: pi1replicate(self, i)
           \/ (\E self \in ProcessesQ: q(self))
           \/ \E self \in ProcessesQ: qsub1(self)
           \/ \E self \in ProcessesQ, i \in SubNodes: qq1replicate(self, i)
           \/ \E self \in ProcessesQ, i \in SubNodes: qi2replicate(self, i)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : SF_vars(p(self))
        /\ \A self \in ProcessesQ : WF_vars(q(self))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Jul 05 07:19:37 GMT 2022 by zunai
\* Created Tue May 31 09:55:09 GMT 2022 by zunai
