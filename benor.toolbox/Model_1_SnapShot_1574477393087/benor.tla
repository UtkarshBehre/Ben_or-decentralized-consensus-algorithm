------------------------------- MODULE benor -------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, F, MAXROUND, INPUT
Procs == 1..N

(*
--algorithm benor
{ variable p1Msg={},    \* message board used to store phase 1 messages
           p2Msg={};    \* message board used to store phase 2 messages

  macro sendP1(n, k, x){    \* used to broadcast proposed values of phase 1 by adding them in message board
    p1Msg := p1Msg \union {[nodeid |->n , r |-> k, value |-> x]};
  }
  macro sendP2(n, k, x){    \* used to broadcast reported values of phase 2 by adding them in message board
    p2Msg := p2Msg \union {[nodeid |->n , r |-> k, value |-> x]};
  }

\* START OF PROCESS
  fair process (p \in Procs)
  variable r=1,
           p1v=INPUT[self],
           p2v=-1,
           decided=-1;
  {         
S:  while(decided=-1 /\ r < MAXROUND){ \* run until value is not decided as 0 or 1, or MAXROUND is reached
      \* PHASE 1
      \* broadcast phase 1 messages  
      sendP1(self, r, p1v);
      \* waits until number of phase 1 messages from non faulty nodes for current round are broadcasted            
P1:   await(Cardinality({ msg \in p1Msg: msg.r = r }) \geq N-F);
      if (Cardinality({msg \in p1Msg: msg.r = r /\ msg.value = 0}) > N \div 2){   \* if majority nodes have value: 0 in current round 
         p2v :=0;   
      }
      else if(Cardinality({msg \in p1Msg: msg.r = r /\ msg.value = 1}) > N \div 2){ \* if majority nodes have value: 1 in current round
         p2v := 1;
      }
      else {    \* if no majority
         p2v := -1;       
      };
      \* PHASE 2
      \* broadcast phase 2 messages
      sendP2(self, r, p2v);
      \* waits until number of phase 2 messages from non faulty nodes for current round are broadcasted
P2:   await(Cardinality({ msg \in p2Msg: msg.r = r }) \geq N-F);
      if(Cardinality({msg \in p2Msg: msg.r = r /\ msg.value = 0}) > F) { \* if value 0 is found in more than F # of nodes  
         decided := 0;
      }
      else if(Cardinality({msg \in p2Msg: msg.r = r /\ msg.value = 1}) > F){ \* if value 1 is found in more than F # of nodes
         decided := 1;
      };
      \* set p1v values for the next round
      if(Cardinality({msg \in p2Msg: msg.r = r /\ msg.value = 0}) > 0) { 
         p1v := 0;
      }
      else if(Cardinality({msg \in p2Msg: msg.r = r /\ msg.value = 1}) > 0){ 
         p1v := 1;
      }
      else { \* if no deterministic value for p1v is found assign a random value 0 or 1
         with ( a \in {0,1} )
            p1v := a; 
      };
      r := r +1;  \* increment r for next round
   };   
 }
}
*)
\* BEGIN TRANSLATION
VARIABLES p1Msg, p2Msg, pc, r, p1v, p2v, decided

vars == << p1Msg, p2Msg, pc, r, p1v, p2v, decided >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ r = [self \in Procs |-> 1]
        /\ p1v = [self \in Procs |-> INPUT[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF decided[self]=-1 /\ r[self] < MAXROUND
                 THEN /\ p1Msg' = (p1Msg \union {[nodeid |->self , r |-> r[self], value |-> p1v[self]]})
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ p1Msg' = p1Msg
           /\ UNCHANGED << p2Msg, r, p1v, p2v, decided >>

P1(self) == /\ pc[self] = "P1"
            /\ (Cardinality({ msg \in p1Msg: msg.r = r[self] }) \geq N-F)
            /\ IF Cardinality({msg \in p1Msg: msg.r = r[self] /\ msg.value = 0}) > N \div 2
                  THEN /\ p2v' = [p2v EXCEPT ![self] = 0]
                  ELSE /\ IF Cardinality({msg \in p1Msg: msg.r = r[self] /\ msg.value = 1}) > N \div 2
                             THEN /\ p2v' = [p2v EXCEPT ![self] = 1]
                             ELSE /\ p2v' = [p2v EXCEPT ![self] = -1]
            /\ p2Msg' = (p2Msg \union {[nodeid |->self , r |-> r[self], value |-> p2v'[self]]})
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << p1Msg, r, p1v, decided >>

P2(self) == /\ pc[self] = "P2"
            /\ (Cardinality({ msg \in p2Msg: msg.r = r[self] }) \geq N-F)
            /\ IF Cardinality({msg \in p2Msg: msg.r = r[self] /\ msg.value = 0}) > F
                  THEN /\ decided' = [decided EXCEPT ![self] = 0]
                  ELSE /\ IF Cardinality({msg \in p2Msg: msg.r = r[self] /\ msg.value = 1}) > F
                             THEN /\ decided' = [decided EXCEPT ![self] = 1]
                             ELSE /\ TRUE
                                  /\ UNCHANGED decided
            /\ IF Cardinality({msg \in p2Msg: msg.r = r[self] /\ msg.value = 0}) > 0
                  THEN /\ p1v' = [p1v EXCEPT ![self] = 0]
                  ELSE /\ IF Cardinality({msg \in p2Msg: msg.r = r[self] /\ msg.value = 1}) > 0
                             THEN /\ p1v' = [p1v EXCEPT ![self] = 1]
                             ELSE /\ \E a \in {0,1}:
                                       p1v' = [p1v EXCEPT ![self] = a]
            /\ r' = [r EXCEPT ![self] = r[self] +1]
            /\ pc' = [pc EXCEPT ![self] = "S"]
            /\ UNCHANGED << p1Msg, p2Msg, p2v >>

p(self) == S(self) \/ P1(self) \/ P2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
--------------------------------------------------------- 
Agreement == (\A i,j \in Procs: decided[i] # -1 /\ decided[j] # -1 => decided[i]=decided[j])
Progress == <>(\A i \in Procs: decided[i] # -1)
BaitProgress == (\E i \in Procs: decided[i] = -1 )  
MinorityReport == (\E i \in Procs: decided[i] # 0)   \* this is correct

\* Input = 0,1,1,1  F= 0 then output wont be zero   because n/2 = 2 and maj  =  n/2 +1 = 3
\*                    F= 1 then output maybe 0  maj = 3  but message currently there are also 3 and should be same
\* Input = 0,1,1   F = 0  then output wont be zero  because n/2 = 1 and maj = n/2 + 1 = 2
\*                 F =1 then output maybe 0 because n/2 = 1 and maj = n/2 + 1 = 2 and both should be same
=============================================================================
\* Modification History
\* Last modified Fri Nov 22 21:48:05 EST 2019 by Utkarsh
\* Created Wed Oct 30 14:47:11 EDT 2019 by Utkarsh

Team Member 1: Name - Utkarsh Behre    |    UBID - 50316972
Team Member 2: Name - Yash Nitin Mantri    |    UBID - 50313926   

Report:

Agreement property:
Ideally, the agreement property should never be violated.
Based on the requirements, Agreement should hold even when F is greater than majority nodes.
So we ran the model with only Agreement being checked to test if Agreement is 
violated or not with the following possible INPUT combinations as below:
    N | F | MAXROUND  | INPUT      |  Holds 
    3 | 1 |     3     | <<1,1,1>>  |  True   
    3 | 1 |     3     | <<0,0,0>>  |  True 
    3 | 2 |     3     | <<0,0,0>>  |  True
    3 | 2 |     4     | <<1,1,1>>  |  True
    3 | 3 |     4     | <<1,1,1>>  |  True
    4 | 2 |     4     |<<1,1,1,1>> |  cur
    4 | 3 |     4     |            |  
    4 | 1 |     3     | <<0,1,1,0>>|   TRUE
    4 | 1 |     4     |          |
    
    
    
Write and test a property to capture the Agreement property of the
consensus protocol. Agreement should always be satisfied, even when
F is more than N/2. Test with N<5 and F < 5, with different values.

Progress property:
Write and test a property to capture the Progress property of the
consensus protocol. If you start with all same preference value at all
nodes, this should terminate.

BaitProgress property: 
Write and test a BaitProgress condition which claims that it is not
possible for all processes to decide (written as a safety property), and
watch the model checker come up with ways progress can happen and
show you that consensus can be solved for some runs

MinorityProgress property: 
If N=4 and INPUT=«0,1,1,1», is it possible to have 0 decided for a run?
Write a safety property called MinorityReport which claims that it
is not possible for all the nodes to finalize with "0" as the consensus
value. The model checker will try to prove you wrong by producing a
counterexample when possible. Check this with F=0, F=1, and F=2.

TODO:
1. 
2. Agreement check if its correct
3. Progress 
4. baitprogress
5. Minority report
6. Comments, add traces for failed scenarios found in baitprogress.
