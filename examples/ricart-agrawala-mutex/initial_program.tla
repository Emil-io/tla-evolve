--------------------------- MODULE initial_program ---------------------------
EXTENDS Naturals, FiniteSets, TLC, Sequences

CONSTANTS Proc

\* *************************************************************************
\* Ricart–Agrawala distributed mutual exclusion, ultra-high level model.
\* - Fixed finite set Proc of process ids.
\* - Each process has a logical clock, a mode (Idle/Requesting/InCS),
\*   and a current request timestamp when Requesting or InCS.
\* - Asynchronous messages (Req/Rep) travel over an abstract network.
\* - Safety: at most one process in the critical section at a time.
\* - Progress: any requesting process eventually enters its critical
\*   section under fair, reliable delivery and no new requests.
\*
\* config file:
\* SPECIFICATION Spec
\*
\* CONSTANTS
\*   \* Example finite process set; adjust as needed for the model run.
\*   Proc = {p1, p2, p3}
\*
\* INVARIANT
\*   TypeOK
\*   Inv_MutualExclusion
\*   Inv_RequestTotalOrder
\*   Inv_ClockMonotone
\*   Inv_CSRequestHighest
\*   Inv_PermitAllBeforeCS
\*   Inv_ReplyOrder
\*   Inv_DeferredEmptyWhenIdle
\*
\* PROPERTY
\*   Prop_MutualExclusion
\*   Prop_PermitAllBeforeCS
\*   Prop_ReplyOrder
\*   Prop_Liveness_EventualEntry
\*   Prop_EachEventuallyCS
\*
\* 
\* *************************************************************************

ModeSet == {"Idle", "Requesting", "InCS"}

Messages ==
  [ mtype : {"Req", "Rep"},
    from  : Proc,
    to    : Proc,
    ts    : Nat ]

Max(S) ==
  CHOOSE x \in S : \A y \in S : x >= y

ProcOrder ==
  CHOOSE f \in [Proc -> 1..Cardinality(Proc)] :
    \A i \in 1..Cardinality(Proc) :
      \E p \in Proc : f[p] = i

(*-----------------------------------------------------------------------*)
(* System specification and fairness                                     *)
(*                                                                       *)
(* We take "Idle" to be the non‑critical section.  As in the             *)
(* DijkstraMutex example, we require weak fairness of each process’s     *)
(* next‑state action only while it is not in the non‑critical section,   *)
(* i.e., while it is trying to enter or is in the critical section.      *)
(*                                                                       *)
(* The PlusCal algorithm below should define:                            *)
(*   - variables  mode, clock, prevClock, reqTS, granted, deferred, net  *)
(*   - process (P \in Proc) ...                                          *)
(* so that the PlusCal translator generates Init, Next, vars, and P(self)*)
(* used in the definition of Spec.                                       *)
(*-----------------------------------------------------------------------*)



\* EVOLVE-BLOCK-START
(*--algorithm RicartAgrawala
variables
  mode = [p \in Proc |-> "Idle"],
  clock = [p \in Proc |-> 0],
  prevClock = [p \in Proc |-> 0],
  reqTS = [p \in Proc |-> 0],
  granted = [p \in Proc |-> {}],
  replies = [p \in Proc |-> {}],
  deferred = [p \in Proc |-> {}],
  net = {};

\* Implement distributed mutual exclusion (Ricart–Agrawala) here.
    

end algorithm;*)
\* EVOLVE-BLOCK-END


HasRequest(p) == mode[p] \in {"Requesting", "InCS"}

Outstanding == { p \in Proc : HasRequest(p) }

ReqKey(p) == << reqTS[p], ProcOrder[p] >>

ReqKeyLT(p, q) ==
  \/ reqTS[p] < reqTS[q]
  \/ /\ reqTS[p] = reqTS[q]
     /\ ProcOrder[p] < ProcOrder[q]

ReqKeyLE(p, q) == ReqKey(p) = ReqKey(q) \/ ReqKeyLT(p, q)

(*************************************************************************)
(* Type correctness and structural assumptions                           *)
(*************************************************************************)

TypeOK ==
  /\ Proc # {}
  /\ IsFiniteSet(Proc)
  /\ mode \in [Proc -> ModeSet]
  /\ clock \in [Proc -> Nat]
  /\ prevClock \in [Proc -> Nat]
  /\ reqTS \in [Proc -> Nat]
  /\ granted \in [Proc -> SUBSET Proc]
  /\ replies \in [Proc -> SUBSET Proc]
  /\ deferred \in [Proc -> SUBSET Proc]
  /\ net \subseteq Messages
  /\ \A p \in Proc : granted[p] \subseteq Proc \ {p}
  /\ \A p \in Proc : deferred[p] \subseteq Proc \ {p}

(*************************************************************************)
(* Invariants (always true properties)                                   *)
(*************************************************************************)

Inv_MutualExclusion ==
  Cardinality({ p \in Proc : mode[p] = "InCS" }) <= 1

Inv_RequestTotalOrder ==
  \A p, q \in Outstanding :
    p = q \/ ReqKeyLT(p, q) \/ ReqKeyLT(q, p)

Inv_ClockMonotone ==
  \A p \in Proc : clock[p] >= prevClock[p]

Inv_CSRequestHighest ==
  \A p \in Outstanding :
    mode[p] = "InCS" =>
      \A q \in Outstanding : ReqKeyLE(p, q)

Inv_PermitAllBeforeCS ==
  \A p \in Proc :
    mode[p] = "InCS" => granted[p] = Proc \ {p}

Inv_ReplyOrder ==
  \A p, q \in Outstanding :
    \A r \in Proc :
      ReqKeyLT(p, q) /\ r \in granted[q] => r \in granted[p]

Inv_DeferredEmptyWhenIdle ==
  \A p \in Proc : mode[p] = "Idle" => deferred[p] = {}

StateConstraint ==
  \A p \in Proc : clock[p] < 7

Inv_All ==
  /\ TypeOK
  /\ Inv_MutualExclusion
  /\ Inv_RequestTotalOrder
  /\ Inv_ClockMonotone
  /\ Inv_CSRequestHighest
  /\ Inv_PermitAllBeforeCS
  /\ Inv_ReplyOrder
  /\ Inv_DeferredEmptyWhenIdle

(*************************************************************************)
(* Safety and liveness properties                                        *)
(*************************************************************************)

Prop_MutualExclusion == []Inv_MutualExclusion

Prop_PermitAllBeforeCS == []Inv_PermitAllBeforeCS

Prop_ReplyOrder == []Inv_ReplyOrder

(* Liveness/progress: under fair, reliable delivery and no new requests, *)
(* every requesting process eventually enters the critical section.       *)
Prop_Liveness_EventualEntry ==
  \A p \in Proc :
    [] (HasRequest(p) => <> (mode[p] = "InCS"))

(* Stronger liveness: every process eventually enters the critical        *)
(* section at some point (not just conditional on requesting).            *)
Prop_EachEventuallyCS ==
  \A p \in Proc : <> (mode[p] = "InCS")

FairSpec ==
  Spec /\ WF_vars(Next)

=============================================================================
