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
fair+ process p = "xProcesses"
begin
     A: x := x+1 ;
     ExA: x := 1 ;
end process
begin
     B: x := x+1 ;
     EXBB: x := 0;
end subprocess
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

\* BEGIN TRANSLATION (chksum(pcal) = "66310879" /\ chksum(tla) = "c81bb3df")
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"xProcesses"} \cup (ProcessesQ)

Genprocs1 == { <<p>>: p \in "xProcesses" }

Genprocs1Thread1 == { <<p,1>>: p \in "xProcesses" }

Genprocs1Thread2 == { <<p,2>>: p \in "xProcesses" }

Genprocs1Thread3 == { <<p,3,i>>: p \in "xProcesses", i \in 4..5}

Genprocs2 == { <<p>>: p \in ProcessesQ }

Genprocs2Thread1 == { <<p,1>>: p \in ProcessesQ }

Genprocs2Thread2 == { <<p,2,q>>: p \in ProcessesQ, q \in SubNodes}

Genprocs2Thread3 == { <<p,3,i>>: p \in ProcessesQ, i \in SubNodes}

SubProcSet == [_n1 \in ProcSet |-> IF _n1 = "xProcesses" THEN 1..4
                               ELSE (**ProcessesQ**) 1..4]

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in Genprocs1 \union Genprocs1Thread1 \union Genprocs1Thread2 \union Genprocs1Thread3 \union Genprocs2 \union Genprocs2Thread1 \union Genprocs2Thread2 \union Genprocs2Thread3 |-> CASE  self \in Genprocs1 -> "A"
		 [] self \in Genprocs1Thread1 -> "B"
		 [] self \in Genprocs1Thread2 -> "N"
		 [] self \in Genprocs1Thread3 -> "BX"
		 [] self \in Genprocs2 -> "D"
		 [] self \in Genprocs2Thread1 -> "E"
		 [] self \in Genprocs2Thread2 -> "F"
		 [] self \in Genprocs2Thread3 -> "G" ]

A == /\ pc[<<"xProcesses" >>] = "A"
     /\ x' = x+1
     /\ pc' = [pc EXCEPT ![<<"xProcesses">>] = "ExA"]

ExA == /\ pc[<<"xProcesses" >>] = "ExA"
       /\ x' = 1
       /\ pc' = [pc EXCEPT ![<<"xProcesses">>] = "Done"]

B == /\ pc[<<"xProcesses" , 1>>] = "B"
     /\ x' = x+1
     /\ pc' = [pc EXCEPT ![<<"xProcesses", 1>>] = "EXBB"]

EXBB == /\ pc[<<"xProcesses" , 1>>] = "EXBB"
        /\ x' = 0
        /\ pc' = [pc EXCEPT ![<<"xProcesses", 1>>] = "Done"]

N == /\ pc[<<"xProcesses" , 2>>] = "N"
     /\ x' = x+1
     /\ pc' = [pc EXCEPT ![<<"xProcesses", 2>>] = "NX"]

NX == /\ pc[<<"xProcesses" , 2>>] = "NX"
      /\ x' = 0
      /\ pc' = [pc EXCEPT ![<<"xProcesses", 2>>] = "Done"]

BX(i) == /\ pc[<<"xProcesses" , 3, i>>] = "BX"
      /\ x' = x+1
      /\ pc' = [pc EXCEPT ![<<"xProcesses", 3, i>>] = "Done"]

p == A \/ ExA

psub1  == B \/ EXBB

psub2  == N \/ NX

pi1replicate( i)  == BX(i)


D(self) == /\ pc[<<self >>] = "D"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self>>] = "ExD"]

ExD(self) == /\ pc[<<self >>] = "ExD"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]

E(self) == /\ pc[<<self , 1>>] = "E"
           /\ x' = x+1
           /\ pc' = [pc EXCEPT ![<<self, 1>>] = "EXTRA"]

EXTRA(self) == /\ pc[<<self , 1>>] = "EXTRA"
               /\ x' = x+1
               /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]

F(self,i) == /\ pc[<<self , 2, i>>] = "F"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self, 2, i>>] = "Done"]

G(self,i) == /\ pc[<<self , 3, i>>] = "G"
             /\ x' = x+1
             /\ pc' = [pc EXCEPT ![<<self, 3, i>>] = "Done"]

q(self) == D(self) \/ ExD(self)

qsub1(self)  == E(self) \/ EXTRA(self)

qq1replicate(self, i)  == F(self, i)

qi2replicate(self, i)  == G(self, i)


Next ==    \/ p
           \/ (\E self \in ProcessesQ: q(self))
           \/ \E self \in ProcessesQ: qsub1(self)
           \/ \E self \in ProcessesQ, i \in SubNodes: qq1replicate(self, i)
           \/ \E self \in ProcessesQ, i \in SubNodes: qi2replicate(self, i)

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(p)
        /\ \A self \in ProcessesQ : WF_vars(q(self))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Jun 16 10:22:55 GMT 2022 by zunai
\* Created Tue May 31 09:55:09 GMT 2022 by zunai
