--------------------------- MODULE ChannelNoClash ---------------------------
EXTENDS Sequences, Naturals

CONSTANTS Coord, Agent

State == {"unknown", "accept", "refuse", "commit", "abort"}

    
(* PlusCal options (-distpcal) *)

(***
--algorithm TPC {
 
  \* message channels
  channels coord, agt[Agent];
     
  fair process (a \in Agent)
  variable aState = "unknown"; {

a1: if (aState = "unknown") {
        with(st \in {"accept", "refuse"}) {
          aState := st;
          send(coord, [type |-> st, agent |-> self]);
        };
    };
    a2: await(aState \in {"commit", "abort"})
    
  } {
    
    a3:await (aState # "unknown");
       receive(agt[self], aState); 
       
    a4:clear(agt);
  }

  fair process (c = Coord) 
  variables cState = "unknown",
            commits = {}, msg = {};
             \* agents that agree to commit
  {
    c1: await(cState \in {"commit", "abort"});    
        broadcast(agt, [ag \in Agent|-> cState]);
  } {
        
     c2:while (cState \notin {"abort", "commit"}) {
        receive(coord, msg);
            if (msg.type = "refuse") {
                cState := "abort";
            }
            else if (msg.type = "accept") {
                commits := commits \cup {msg.agent};
                 if (commits = Agent) {
                    cState := "commit";
                 }
              }
        }
  }
 }
***)



\* BEGIN TRANSLATION (chksum(pcal) = "66784c41" /\ chksum(tla) = "ed62fe55")
VARIABLES coord, agt, pc, aState, cState, commits, msg

vars == << coord, agt, pc, aState, cState, commits, msg >>

ProcSet == (Agent) \cup {Coord}

Genprocs1 == { <<p>>: p \in Agent }

Genprocs1Thread1 == { <<p,1>>: p \in Agent }

Genprocs2 == { <<p>>: p \in Coord }

Genprocs2Thread1 == { <<p,1>>: p \in Coord }

Init == (* Global variables *)
        /\ coord = {}
        /\ agt = [_n10 \in Agent |-> {}]
        (* Process a *)
        /\ aState = [self \in Agent |-> "unknown"]
        (* Process c *)
        /\ cState = "unknown"
        /\ commits = {}
        /\ msg = {}
        /\ pc = [self \in Genprocs1 \union Genprocs1Thread1 \union Genprocs2 \union Genprocs2Thread1 |-> CASE  self \in Genprocs1 -> "a1"
		 [] self \in Genprocs1Thread1 -> "a3"
		 [] self \in Genprocs2 -> "c1"
		 [] self \in Genprocs2Thread1 -> "c2" ]

a1(self) == /\ pc[<<self >>] = "a1"
            /\ IF aState[self] = "unknown"
                  THEN /\ \E st \in {"accept", "refuse"}:
                            /\ aState' = [aState EXCEPT ![self] = st]
                            /\ coord' = (coord \cup {[type |-> st, agent |-> self]})
                  ELSE /\ TRUE
                       /\ UNCHANGED << coord, aState >>
            /\ pc' = [pc EXCEPT ![<<self>>] = "a2"]
            /\ UNCHANGED << agt, cState, commits, msg >>

a2(self) == /\ pc[<<self >>] = "a2"
            /\ (aState[self] \in {"commit", "abort"})
            /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
            /\ UNCHANGED << coord, agt, aState, cState, commits, msg >>

a3(self) == /\ pc[<<self , 1>>] = "a3"
            /\ (aState[self] # "unknown")
            /\ \E _a1519 \in agt[self]:
                 /\ aState' = [aState EXCEPT ![self] = _a1519]
                 /\ agt' = [agt EXCEPT ![self] = @ \ {_a1519}]
            /\ pc' = [pc EXCEPT ![<<self, 1>>] = "a4"]
            /\ UNCHANGED << coord, cState, commits, msg >>

a4(self) == /\ pc[<<self , 1>>] = "a4"
            /\ agt' = [_a0 \in Agent |-> {}]
            /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
            /\ UNCHANGED << coord, aState, cState, commits, msg >>

a(self) == a1(self) \/ a2(self)

asub1(self)  == a3(self) \/ a4(self)


c1(self) == /\ pc[<<self >>] = "c1"
            /\ (cState \in {"commit", "abort"})
            /\ agt' = [ag \in Agent |-> agt[ag] \cup  {cState} ]
            /\ pc' = [pc EXCEPT ![<<self>>] = "Done"]
            /\ UNCHANGED << coord, aState, cState, commits, msg >>

c2(self) == /\ pc[<<self , 1>>] = "c2"
            /\ IF cState \notin {"abort", "commit"}
                  THEN /\ \E _c1512 \in coord:
                            /\ coord' = coord \ {_c1512}
                            /\ msg' = _c1512
                       /\ IF msg'.type = "refuse"
                             THEN /\ cState' = "abort"
                                  /\ UNCHANGED commits
                             ELSE /\ IF msg'.type = "accept"
                                        THEN /\ commits' = (commits \cup {msg'.agent})
                                             /\ IF commits' = Agent
                                                   THEN /\ cState' = "commit"
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED cState
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << cState, commits >>
                       /\ pc' = [pc EXCEPT ![<<self, 1>>] = "c2"]
                  ELSE /\ pc' = [pc EXCEPT ![<<self, 1>>] = "Done"]
                       /\ UNCHANGED << coord, cState, commits, msg >>
            /\ UNCHANGED << agt, aState >>

c(self) == c1(self)

csub1(self)  == c2(self)


Next ==    \/ (\E self \in Agent: a(self))
           \/ \E self \in Agent: asub1(self)

Spec == /\ Init /\ [][Next]_vars


\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Jul 03 10:14:46 GMT 2022 by zunai
\* Created Fri Jun 24 10:31:53 GMT 2022 by zunai
