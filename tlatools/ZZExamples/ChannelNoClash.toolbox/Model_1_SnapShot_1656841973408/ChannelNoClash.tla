--------------------------- MODULE ChannelNoClash ---------------------------


EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat 
Nodes == 1 .. N

(* PlusCal options (-distpcal) *)

(*
--algorithm LamportMutex {

variables _n = 1,
          _n1 = 3;
          _n30 = 3;
          n1 = 2;
channel chan[Nodes], ch[Nodes,Nodes];
fifo fif[Nodes], f;

process (x = N+1)
variables t = <<1,2,3   >>;
{
    One:
           t[1] := 1; 
    Sdr1:
        send(chan[1], "msg");
} 

process (id \in Nodes)
variables s = [no \in Nodes |-> 1];
{
    Two:
           s[self] := 2;
    Sdr2:
        send(chan[self], "msg");
}

}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "d83ccee9" /\ chksum(tla) = "6c3a24a8")
VARIABLES _n, _n1, _n30, n1, chan, ch, fif, f, pc, t, s

vars == << _n, _n1, _n30, n1, chan, ch, fif, f, pc, t, s >>

ProcSet == {N+1} \cup (Nodes)

Genprocs1 == { <<p>>: p \in N+1 }

Genprocs2 == { <<p>>: p \in Nodes }

Init == (* Global variables *)
        /\ _n = 1
        /\ _n1 = 3
        /\ _n30 = 3
        /\ n1 = 2
        /\ chan = [_n10 \in Nodes |-> {}]
        /\ ch = [_n20 \in Nodes, _n31 \in Nodes |-> {}]
        /\ fif = [_n40 \in Nodes |-> <<>>]
        /\ f = <<>>
        (* Process x *)
        /\ t = <<1,2,3   >>
        (* Process id *)
        /\ s = [self \in Nodes |-> [no \in Nodes |-> 1]]
        /\ pc = [self \in Genprocs1 \union Genprocs2 |-> CASE  self \in Genprocs1 -> "One"
		 [] self \in Genprocs1 -> "Two" ]

One(self) == /\ pc[<<self >>] = "One"
             /\ t' = [t EXCEPT ![1] = 1]
             /\ pc' = [pc EXCEPT ![<<self>>] = "Sdr1"]
             /\ UNCHANGED << _n, _n1, _n30, n1, chan, ch, fif, f, s >>

Sdr1(self) == /\ pc[<<self >>] = "Sdr1"
              /\ chan' = [chan EXCEPT ![1] = @ \cup {"msg"}]
              /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
              /\ UNCHANGED << _n, _n1, _n30, n1, ch, fif, f, t, s >>

x(self) == One(self) \/ Sdr1(self)


Two(self) == /\ pc[<<self >>] = "Two"
             /\ s' = [s EXCEPT ![self][self] = 2]
             /\ pc' = [pc EXCEPT ![<<self>>] = "Sdr2"]
             /\ UNCHANGED << _n, _n1, _n30, n1, chan, ch, fif, f, t >>

Sdr2(self) == /\ pc[<<self >>] = "Sdr2"
              /\ chan' = [chan EXCEPT ![self] = @ \cup {"msg"}]
              /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
              /\ UNCHANGED << _n, _n1, _n30, n1, ch, fif, f, t, s >>

id(self) == Two(self) \/ Sdr2(self)


Next ==    \/ (\E self \in Nodes: id(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Jul 03 09:41:27 GMT 2022 by zunai
\* Created Fri Jun 24 10:31:53 GMT 2022 by zunai
