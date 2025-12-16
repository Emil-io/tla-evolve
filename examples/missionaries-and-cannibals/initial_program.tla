---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC, Sequences

Missionaries == {"M1", "M2", "M3"}
Cannibals    == {"C1", "C2", "C3"}
People       == Missionaries \cup Cannibals

(* --algorithm MissionariesAndCannibals {
\* Implement the Missionaries & Cannibals river-crossing puzzle here (reach all-across safely).
} *)

CountM(S) == Cardinality(S \cap Missionaries)
CountC(S) == Cardinality(S \cap Cannibals)
SafeBank(S) == (CountM(S) = 0) \/ (CountM(S) >= CountC(S))

FairSpec == Spec /\ WF_vars(Next)

\* Invariants
TypeOK ==
  /\ left \subseteq People /\ right \subseteq People
  /\ left \cap right = {}
  /\ left \cup right = People
  /\ boat \in {"left","right"}

Safe ==
  /\ SafeBank(left)
  /\ SafeBank(right)

AllStartRight==
  /\ left = People
  /\ right = {}
  /\ boat = "right"

InitialConditionOK == Init => AllStartLeft

Passengers ==
  IF boat = "left" THEN left \ left' ELSE right \ right'

ProperMove ==
  /\ boat' # boat
  /\ Cardinality(Passengers) \in {1, 2}
  /\ IF boat = "left" THEN
        /\ left'  = left \ Passengers
        /\ right' = right \cup Passengers
     ELSE
        /\ right' = right \ Passengers
        /\ left'  = left \cup Passengers

ProperBoatMove ==
  [] [Next => (UNCHANGED <<left, right, boat>> \/ ProperMove)]_vars

AllAcross == right = People
ReachGoal == <>AllAcross


==== 