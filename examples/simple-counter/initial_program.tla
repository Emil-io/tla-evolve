---- MODULE Simple ----
EXTENDS Naturals, TLC

\* EVOLVE-BLOCK-START
(* --algorithm SimpleAlgo {

\* Implement a simple counter here (e.g., count up from 0 within bounds).

} *)
\* EVOLVE-BLOCK-END

\* Invariant(s)
SafeBounds == x \in 0..10

\* Property(s)
CountsUp == (x = 0) /\ (\A k \in 0..9 : ((x = k) ~> (x = k + 1)))

FairSpec == Spec /\ WF_vars(Next)

====


