------------------------ MODULE SingleProcessIn -------------------------
EXTENDS TLC, Integers, Sequences
CONSTANTS P
ASSUME P \in Nat
Nodes == 1..P
SubNodes == 1..2
Three == 1..4

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo

variables x;

process rm \in Nodes
begin
   start: 
        x := x+1;
end process;
begin 
   Z: x := 1;
end subprocess;
begin
  replicate i \in SubNodes;
     x := 0;
end subprocess;
process second \in Nodes
begin
  SProc: x := x + 1
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "84956a92" /\ chksum(tla) = "c3a599eb")
CONSTANT defaultInitValue
VARIABLES x, pc

vars == << x, pc >>

ProcSet == (Nodes) \cup (Nodes)

SubProcSet == [_n1 \in ProcSet |-> IF _n1 \in Nodes THEN 1..3
                                 ELSE (**Nodes**) 1..1]
ReplicateProc1 == (SubNodes)
ReplicateProc2 == 0
ReplicateSet == [i \in ReplicateProc1|-> IF i \in SubNodes THEN 4..5
                                 ELSE (**null**) 1..1]
definit == [i \in ReplicateSet |-> IF i \in SubNodes THEN i
                                                   ELSE 1]

Init == (* Global variables *)
        /\ x = defaultInitValue
        /\ pc = [self \in ProcSet \union  SubNodes |-> CASE self \in Nodes /\ self \in SubNodes
                                                        -> <<"start","Z","Lbl_1">> /\ <<self>>
                                                        
                           [] self \in Nodes /\ self = 1 -> <<"SProc">> /\ <<1>>]

start(self) == /\ pc[self][1][1]  = "start"
               /\ x' = x+1
               /\ pc' = [pc EXCEPT ![self][1][1] = "Done"]

Z(self) == /\ pc[self][2][1]  = "Z"
           /\ x' = 1
           /\ pc' = [pc EXCEPT ![self][2][1] = "Done"]

Lbl_1(self, i) == /\ pc[self][3][i]  = "Lbl_1"
               /\ x' = 0
               /\ pc' = [pc EXCEPT ![self][3][i] = "Done"]

rm(self, i) == start(self) \/ Z(self) \/ Lbl_1(self, i)

SProc(self) == /\ pc[self][1][1]  = "SProc"
               /\ x' = x + 1
               /\ pc' = [pc EXCEPT ![self][1][1] = "Done"]

second(self) == SProc(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub][1] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes, i \in SubNodes: rm(self, i))
           \/ (\E self \in Nodes: second(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION 
==========================================================
