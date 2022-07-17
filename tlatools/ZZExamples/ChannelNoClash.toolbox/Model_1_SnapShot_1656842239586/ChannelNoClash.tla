--------------------------- MODULE ChannelNoClash ---------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm message_queue {

variables ar = [i \in 1..2 |-> 3];
fifo chan[Nodes];

macro send_to(i, msg) {
  ar[i] := ar[i]+1;
  \* send(chan[i], msg);
}


process ( w \in Nodes )
{
    Mc:
        send_to(self, "abc");
}


}
*)



\* BEGIN TRANSLATION (chksum(pcal) = "6f4d255c" /\ chksum(tla) = "4542f6df")
VARIABLES ar, chan, pc

vars == << ar, chan, pc >>

ProcSet == (Nodes)

Genprocs1 == { <<p>>: p \in Nodes }

Init == (* Global variables *)
        /\ ar = [i \in 1..2 |-> 3]
        /\ chan = [_n10 \in Nodes |-> <<>>]
        /\ pc = [self \in Genprocs1 |-> "Mc" ]

Mc(self) == /\ pc[<<self >>] = "Mc"
            /\ ar' = [ar EXCEPT ![self] = ar[self]+1]
            /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
            /\ chan' = chan

w(self) == Mc(self)


Next ==    \/ (\E self \in Nodes: w(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Jul 03 09:56:37 GMT 2022 by zunai
\* Created Fri Jun 24 10:31:53 GMT 2022 by zunai
