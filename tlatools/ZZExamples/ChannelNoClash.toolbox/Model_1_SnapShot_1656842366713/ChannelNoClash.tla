--------------------------- MODULE ChannelNoClash ---------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT N
ASSUME N \in Nat
Nodes == 1 .. N
reader == 1..4
writer == 5..9

(* PlusCal options (-distpcal) *)

(*
--algorithm chan_msg_algo

variable cur = "none";
channel chan;

process w \in writer
begin
    Write:
    while ( TRUE ) do
            send(chan, "msg");
    end while;
end process;

process r \in reader
begin
    Read:
    while ( TRUE ) do
            receive(chan, cur);
    end while;
end process;

end algorithm;
*)



\* BEGIN TRANSLATION (chksum(pcal) = "35502056" /\ chksum(tla) = "61607bc5")
VARIABLES cur, chan, pc

vars == << cur, chan, pc >>

ProcSet == (writer) \cup (reader)

Genprocs1 == { <<p>>: p \in writer }

Genprocs2 == { <<p>>: p \in reader }

Init == (* Global variables *)
        /\ cur = "none"
        /\ chan = {}
        /\ pc = [self \in Genprocs1 \union Genprocs2 |-> CASE  self \in Genprocs1 -> "Write"
		 [] self \in Genprocs1 -> "Read" ]

Write(self) == /\ pc[<<self >>] = "Write"
               /\ chan' = (chan \cup {"msg"})
               /\ pc' = [pc EXCEPT ![<<self>>] = "Write"]
               /\ cur' = cur

w(self) == Write(self)


Read(self) == /\ pc[<<self >>] = "Read"
              /\ \E _c169 \in chan:
                   /\ chan' = chan \ {_c169}
                   /\ cur' = _c169
              /\ pc' = [pc EXCEPT ![<<self>>] = "Read"]

r(self) == Read(self)


Next ==    \/ (\E self \in writer: w(self))
           \/ (\E self \in reader: r(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Jul 03 09:58:57 GMT 2022 by zunai
\* Created Fri Jun 24 10:31:53 GMT 2022 by zunai
