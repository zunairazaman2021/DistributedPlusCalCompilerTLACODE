----------------------------- MODULE TwoThreads -----------------------------
EXTENDS Naturals, TLC
(* PlusCal options (-distpcal) *)
(*
--algorithm threads {
  variables x=0, y=0;
  
  process (thread1 = "thr1")
  { start1:  skip; \* Do nothing at beginning
    1a: if ( y=0 ) {
    1b:     x:=1; } ;
    end1a: if (pc["thr1"][2] = "Done") { \* If other guy is done
          print <<"x, y:", x, y>> ;
    end1b:   assert ~(x=1 /\ y=1) ; \* Condition "not(x==1 && y==1)" can fail
        }
  } \* end process block
  
  { start2:  skip; \* Do nothing at beginning
    2a: if ( x=0 ) {
    2b:     y:=1; } ;
    end2a: if (pc["thr1"][1] = "Done") { \* If other guy is done
          print <<"x, y:", x, y>> ;
    end2b:   assert ~(x=1 /\ y=1) ; \* Condition "not(x==1 && y==1)" can fail
        }
  } \* end process block

  } \* end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-84411f740aabc6f8efc36490d28240b7
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == {"thr1"}

SubProcSet == [_n1 \in ProcSet |-> 1..2]

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ pc = [self \in ProcSet |-> <<"start1","start2">>]

start1 == /\ pc["thr1"][1]  = "start1"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["thr1"][1] = "1a"]
          /\ UNCHANGED << x, y >>

1a == /\ pc["thr1"][1]  = "1a"
      /\ IF y=0
            THEN /\ pc' = [pc EXCEPT !["thr1"][1] = "1b"]
            ELSE /\ pc' = [pc EXCEPT !["thr1"][1] = "end1a"]
      /\ UNCHANGED << x, y >>

1b == /\ pc["thr1"][1]  = "1b"
      /\ x' = 1
      /\ pc' = [pc EXCEPT !["thr1"][1] = "end1a"]
      /\ y' = y

end1a == /\ pc["thr1"][1]  = "end1a"
         /\ IF pc["thr1"][2] = "Done"
               THEN /\ PrintT(<<"x, y:", x, y>>)
                    /\ pc' = [pc EXCEPT !["thr1"][1] = "end1b"]
               ELSE /\ pc' = [pc EXCEPT !["thr1"][1] = "Done"]
         /\ UNCHANGED << x, y >>

end1b == /\ pc["thr1"][1]  = "end1b"
         /\ Assert(~(x=1 /\ y=1), 
                   "Failure of assertion at line 14, column 14.")
         /\ pc' = [pc EXCEPT !["thr1"][1] = "Done"]
         /\ UNCHANGED << x, y >>

start2 == /\ pc["thr1"][2]  = "start2"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["thr1"][2] = "2a"]
          /\ UNCHANGED << x, y >>

2a == /\ pc["thr1"][2]  = "2a"
      /\ IF x=0
            THEN /\ pc' = [pc EXCEPT !["thr1"][2] = "2b"]
            ELSE /\ pc' = [pc EXCEPT !["thr1"][2] = "end2a"]
      /\ UNCHANGED << x, y >>

2b == /\ pc["thr1"][2]  = "2b"
      /\ y' = 1
      /\ pc' = [pc EXCEPT !["thr1"][2] = "end2a"]
      /\ x' = x

end2a == /\ pc["thr1"][2]  = "end2a"
         /\ IF pc["thr1"][1] = "Done"
               THEN /\ PrintT(<<"x, y:", x, y>>)
                    /\ pc' = [pc EXCEPT !["thr1"][2] = "end2b"]
               ELSE /\ pc' = [pc EXCEPT !["thr1"][2] = "Done"]
         /\ UNCHANGED << x, y >>

end2b == /\ pc["thr1"][2]  = "end2b"
         /\ Assert(~(x=1 /\ y=1), 
                   "Failure of assertion at line 23, column 14.")
         /\ pc' = [pc EXCEPT !["thr1"][2] = "Done"]
         /\ UNCHANGED << x, y >>

thread1 == start1 \/ 1a \/ 1b \/ end1a \/ end1b \/ start2 \/ 2a \/ 2b
              \/ end2a \/ end2b

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : \A sub \in SubProcSet[self]: pc[self][sub] = "Done"
               /\ UNCHANGED vars

Next == thread1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: \A sub \in SubProcSet[self] : pc[self][sub] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ea8b5c79831b4e3a49cee579b68728ac


=============================================================================
\* Modification History
\* Last modified Mon Apr 25 12:32:40 GMT 2022 by zunai
\* Created Mon Apr 25 08:12:47 GMT 2022 by zunai
