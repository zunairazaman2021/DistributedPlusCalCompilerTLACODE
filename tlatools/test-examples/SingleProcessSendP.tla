------------------------ MODULE SingleProcessSendP -------------------------
EXTENDS TLC, Integers, Sequences

(* PlusCal options (-distpcal) *)

(*
--algorithm seq_algo

channel chan;

process rm = 1
begin
	Start:
	send(chan, 2);
end process;
begin
  threadpro: send(chan, 3)
end subprocess

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "92c4ca70" /\ chksum(tla) = "3506b569")
VARIABLES chan, pc

vars == << chan, pc >>

ProcSet == {1}

SubProcSet == [_n1 \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ chan = {}
        /\ pc = [self \in ProcSet |-> <<"Start","threadpro">>]

Start == /\ pc[1][1]  = "Start"
         /\ chan' = (chan \cup {2})
         /\ pc' = [pc EXCEPT ![1][1] = "Done"]

threadpro == /\ pc[1][2]  = "threadpro"
             /\ chan' = (chan \cup {3})
             /\ pc' = [pc EXCEPT ![1][2] = "Done"]

rm == Start \/ threadpro

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == rm
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION


==========================================================
