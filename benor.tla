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
S:  while(r < MAXROUND){ \* run until value is not decided as 0 or 1, or MAXROUND is reached
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
           /\ IF r[self] < MAXROUND
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
MinorityReport == (\E i \in Procs: decided[i] # 0)
=============================================================================
\* Modification History
\* Last modified Sat Nov 23 01:17:35 EST 2019 by Utkarsh
\* Created Wed Oct 30 14:47:11 EDT 2019 by Utkarsh

Team Member 1: Name - Utkarsh Behre        |    UBID - 50316972
Team Member 2: Name - Yash Nitin Mantri    |    UBID - 50313926   


Agreement property:

Agreement property states that, once all the processes have decided a value, then that value should be same for all of them.
In other words, if any 2 processes, say i and j have made their decisions say d1 and d2, respectively, then d1 and d2 have to be equal (i.e. d1 = d2)
In our implementation of the property above, we check if for 2 processes, decided is not equal to -1 (meaning that processes has decided on some value ( 0 or 1))
then we check if both decided values for both processes are the same.
  
As per the requirements, the Agreement property of the consensus protocol should never be violated.
Based on the requirements, Agreement should hold even when F is greater than majority nodes.
So we ran the model to test if Agreement is violated or not 
with the following possible combinations of input to the model as below:

    N | F | MAXROUND  | INPUT      |  Agreement Holds 
    3 | 1 |     3     | <<1,1,1>>  |  TRUE   
    3 | 1 |     3     | <<0,0,0>>  |  TRUE 
    3 | 2 |     3     | <<0,1,1>>  |  TRUE
    3 | 2 |     4     | <<1,1,1>>  |  TRUE
    3 | 3 |     4     | <<1,1,1>>  |  TRUE
    4 | 1 |     3     | <<0,1,1,0>>|  TRUE    
    4 | 3 |     3     |<<1,1,1,1>> |  TRUE
    4 | 4 |     3     |<<1,1,1,1>> |  TRUE
    4 | 3 |     3     |<<0,1,1,1>> |  TRUE
    4 | 3 |     3     |<<0,1,0,1>> |  TRUE
    4 | 2 |     4     |<<1,1,1,1>> |  TRUE
    4 | 3 |     3     |<<0,1,1,1>> |  TRUE
    4 | 4 |     3     |<<0,1,1,1>> |  TRUE
    4 | 3 |     4     |<<0,0,1,1>> |  TRUE

As per our findings in all the combinations where F less or more than majority of nodes ( some cases even equal to N ), 
the property Agreement never got violated.


Progress property:

Progress property of the consensus protocol states that eventually all proccess end up deciding some final value and then the program would terminate.
So in our implementation of the property above, we check for all processes to have decided value anything other than -1.

As per the requirements, we tested the Progress property by starting with same preference value at all nodes with different N, F values.
The different combination of the input to the model that we tried are given below.

    N | F | MAXROUND  | INPUT        |  Progress Holds
    1 | 0 |     4     | <<1>>        |  TRUE
    2 | 0 |     4     | <<0,0>>      |  TRUE
    3 | 0 |     4     | <<1,1,1>>    |  TRUE
    3 | 1 |     4     | <<0,0,0>>    |  TRUE 
    4 | 0 |     4     | <<1,1,1,1>>  |  TRUE
    4 | 1 |     4     | <<0,0,0,0>>  |  TRUE   
    5 | 1 |     3     | <<0,0,0,0,0>>|  TRUE
As per our findings, the Progress property holds true when we start all nodes with same preference value and termination is reached.


BaitProgress property:

BaitProgress property states that initially it is not possible for all processes to decide a value, but eventually the model 
checker shows that progress can happen and consensus can be solved after some runs.
The BaitProgress property should get violated if the model checker proves the progress happens such that the decided values for all nodes
are no longer -1 and program terminates.
The way we implemented the above is exactly as per above statement. We baited model checker to show us the state trace for which the 
progress is achieved and termination occured by saying that we always have atleast one decision value as -1 ( which would be violated 
eventually). 

So as soon as the model checker finds a state where all the decided values are something other than -1, then it shows BaitProgress 
property is violated and it shows us the trace for the same.

We tried many combinations of inputs with different N, F, and INPUT values. The column "BaitProgress Holds"'s value is False meaning that 
BaitProgress got violated and we got some trace given by the model checker. And if a trace was given by the model checker, we see a TRUE
value in the "State trace showed" column.

 Case #  | N | F | MAXROUND  | INPUT        |  BaitProgress Holds  |    State trace showed
   1.    | 1 | 0 |     4     | <<1>>        |  FALSE               |    TRUE
   2.    | 2 | 0 |     4     | <<1,1>>      |  FALSE               |    TRUE
   3.    | 2 | 0 |     4     | <<0,1>>      |  FALSE               |    TRUE
   4.    | 3 | 1 |     4     | <<1,1,0>>    |  FALSE               |    TRUE
   5.    | 4 | 0 |     4     | <<0,0,1,1>>  |  FALSE               |    TRUE
   6.    | 4 | 1 |     4     | <<0,0,1,1>>  |  FALSE               |    TRUE
   7.    | 4 | 1 |     4     | <<0,1,1,1>>  |  FALSE               |    TRUE

First lets look at the trace found for the case 4 above, where N = 3, F = 1, MAXROUND = 4, and INPUT = <<1,1,0>> 
PC simply tells the current label states for all the processes. For case 4 we only have 3 processes and the trace shown by the model 
checker is shown in the below table.
   
   Case 4 State trace with decided values of the processes
State num |      PC    |       Decided
    1     |   S, S, S  |       -1,-1,-1
    2     |   P1,S, S  |       -1,-1,-1
    3     |   P1,P1,S  |       -1,-1,-1
    4     |   P2,P1,S  |       -1,-1,-1
    5     |   P2,P2,S  |       -1,-1,-1
    6     |   S, P2,S  |        1,-1,-1
    7     |   S, S, S  |        1, 1,-1
    8     |   S, S, P1 |        1, 1,-1
    9     |   S, S, P2 |        1, 1,-1
   10     |   S, S, S  |        1, 1, 1

So for the case 4, we can see that process 3 was not part of the phases in the first round, but it caught up with the value 1 in 
the next round. So the progress was achieved eventually even though a node was missed out on a commit.

Now lets take a look at a more interesting case, that is case 6 where N = 4, F = 1, MAXROUND = 4, and INPUT = <<0,0,1,1>>
The state trace that was given by the model checker is given below:
   
   Case 6 State trace with decided values of the processes
State num |       PC       |      Decided
    1     |    S, S, S, S  |    -1,-1,-1,-1
    2     |   P1, S, S, S  |    -1,-1,-1,-1
    3     |   P1,P1, S, S  |    -1,-1,-1,-1
    4     |   P1,P1, S,P1  |    -1,-1,-1,-1
    5     |   P2,P1, S,P1  |    -1,-1,-1,-1
    6     |   P2,P2, S,P1  |    -1,-1,-1,-1
    7     |   P2,P2,P1,P1  |    -1,-1,-1,-1
    8     |   P2,P2,P2,P1  |    -1,-1,-1,-1
    9     |    S,P2,P2,p1  |    -1,-1,-1,-1
   10     |   P1,P2,P2,P1  |    -1,-1,-1,-1
   11     |   P1, S,P2,P1  |    -1,-1,-1,-1
   12     |   P1,P1,P2,P1  |    -1,-1,-1,-1
   13     |   P1,P1, S,P1  |    -1,-1,-1,-1
   14     |   P1,P1,P1,P1  |    -1,-1,-1,-1
   15     |   P2,P1,P1,P1  |    -1,-1,-1,-1
   16     |   P2,P2,P1,P1  |    -1,-1,-1,-1
   17     |   P2,P2,P2,P1  |    -1,-1,-1,-1
   18     |    S,P2,P2,P1  |     0,-1,-1,-1
   19     |    S, S,P2,P1  |     0, 0,-1,-1
   20     |    S, S,P2,P2  |     0, 0,-1,-1
   21     |    S, S,P2, S  |     0, 0,-1,-1
   22     |    S, S, S, S  |     0, 0, 0,-1
   23     |    S, S, S,P1  |     0, 0, 0,-1
   24     |    S, S, S,P2  |     0, 0, 0,-1
   25     |    S, S, S, S  |     0, 0, 0, 0
                    
This case looks particularly interesting as it took several rounds to reach to a consensus for any couple of nodes. In this case model kept
failing to get majority nodes to come to an agreement initially as it kept assigning same values by random chance that was already there. 
But finally at state number 18, we can see that majority finally agreed on the value 0. This happened because random value assignment done in
the previous round actually gave a different value than what was there already.
As per state numbers 18 and 19 we see that processes 1 and 2 got their values decided as 0. Process P3 catches up later at state 22. But 
since the process 4 was still in an old round it couldn't get the value 0 by majority at this point. Later on in the next round, the process 4 
eventually caught up with other nodes and got the value 0.

So, we got the state trace of the way progress happened when the property BaitProgress failed by the model checker proving that progress does 
happen and termination occurs eventually resulting in the consensus being achieved.


MinorityReport property:

MinorityReport Property states that for a set of nodes, if initial INPUT values have a minority value 0, then it is not possible for the 
nodes to decide 0 eventually. However, it is possible to decide value 0 if there are enough faulty nodes to make the value 0 not minority
in the nodes. This is proven by our findings below in the case 2 and case 3 where the MinorityReport property fails and the model checker decides
value 0 eventually.

In our implementation we say that the model cannot decide 0 for all nodes for the given Minority INPUT. 

 Case # | N | F | MAXROUND  | INPUT        |  MinorityReport Holds|    Model Checker showed that 0 was decided for a run
   1.   | 4 | 0 |     4     | <<0,1,1,1>   |  TRUE                |    FALSE
   2.   | 4 | 1 |     4     | <<0,1,1,1>   |  FALSE               |    TRUE
   3.   | 4 | 2 |     4     | <<0,1,1,1>>  |  FALSE               |    TRUE  
   
State trace for Case 2: N = 4, F = 1, MAXROUND = 4, and INPUT = <<0,1,1,1>> as shown by the model checker is given below.
  
 State num |     PC           |     Decided
     1     |   S, S, S, S     |   -1,-1,-1,-1
     2     |  P1, S, S, S     |   -1,-1,-1,-1
     3     |  P1,P1, S, S     |   -1,-1,-1,-1
     4     |  P1,P1,P1, S     |   -1,-1,-1,-1
     5     |  P2,P1,P1, S     |   -1,-1,-1,-1
     6     |  P2,P2,P1, S     |   -1,-1,-1,-1
     7     |  P2,P2,P2, S     |   -1,-1,-1,-1
     8     |   S,P2,P2, S     |   -1,-1,-1,-1
     9     |  P1,P2,P2, S     |   -1,-1,-1,-1
    10     |  P1, S,P2, S     |   -1,-1,-1,-1
    11     |  P1,P1,P2, S     |   -1,-1,-1,-1
    12     |  P1,P1, S, S     |   -1,-1,-1,-1
    13     |  P1,P1,P1, S     |   -1,-1,-1,-1
    14     |  P2,P1,P1, S     |   -1,-1,-1,-1
    15     |  P2,P2,P1, S     |   -1,-1,-1,-1
    16     |  P2,P2,P2, S     |   -1,-1,-1,-1
    17     |   S,P2,P2, S     |    0,-1,-1,-1
    18     |   S, S,P2, S     |    0, 0,-1,-1
    19     |   S, S, S, S     |    0, 0, 0,-1
    20     |   S, S, S,p1     |    0, 0, 0,-1
    21     |   S, S, S,P2     |    0, 0, 0,-1
    22     |   S, S, S, S     |    0, 0, 0,-1
    23     |   S, S, S,P1     |    0, 0, 0,-1
    24     |   S, S, S,P2     |    0, 0, 0,-1
    25     |   S, S, S, S     |    0, 0, 0, 0

In this case, initially, 0 value could not be decided as the majority. But, since there was a faulty node so model checker coudn't make up
a majority value right away, and starts assigning random values to the nodes. Now based on these assignments, the model checker failed to get
majority uptil the state 16. At this point it did end up getting 0 as the majority value and decided the same for nodes 1,2, and 3. The last
node 4 also ended up getting this value 0 after 2 rounds at the 25th state step.

So, as per our findings for the case above we can see that the the model checker eventually ends up deciding value 0 for all nodes and it was
possible to have 0 decided for a run for the N = 4 and INPUT=<<0,1,1,1>>.