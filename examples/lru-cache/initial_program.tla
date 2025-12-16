--------------------------- MODULE LRUCache ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Keys, Values, Capacity, Requests, NoKey

ElemSet(s) == { s[i] : i \in 1..Len(s) }

\* Convenience alias used by invariants
ToSet(s) == ElemSet(s)

IsUnique(seq) == \A i, j \in 1..Len(seq): i # j => seq[i] # seq[j]

\* Fixed request trace used by the default TLC model.
RequestSeq ==
  << [op |-> "put", key |-> 1, val |-> 10],
     [op |-> "put", key |-> 2, val |-> 20],
     [op |-> "get", key |-> 1],
     [op |-> "put", key |-> 3, val |-> 30] >>

\* EVOLVE-BLOCK-START
(* --algorithm LRUAlgo
 {
   variables present = {},
             values = [kk \in Keys |-> CHOOSE vv \in Values: TRUE],
             order = << >>,
             i = 0,
             lastAccess = [kk \in Keys |-> 0],
             evicted = NoKey;

  \* Implement an LRU cache (handle get/put requests with eviction) here.
  skip;
 }
*)
\* EVOLVE-BLOCK-END

\* Invariants (safety properties)
TypeOK ==
  /\ present \subseteq Keys
  /\ values \in [Keys -> Values]
  /\ order \in Seq(Keys)
  /\ i \in 0..Len(Requests)
  /\ lastAccess \in [Keys -> 0..Len(Requests)]
  /\ evicted \in (Keys \cup {NoKey})

CapacityBound == Len(order) <= Capacity

OrderMatchesPresent ==
  /\ IsUnique(order)
  /\ ToSet(order) = present

====


