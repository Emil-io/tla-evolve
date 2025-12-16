---- MODULE BipartiteMatching ----
\* EVOLVE-BLOCK-START
EXTENDS Naturals, FiniteSets, TLC, Sequences

(*
Config file:
<config>
SPECIFICATION FairSpec

INVARIANTS
  GraphOK
  TypeOK
  NoSharedEndpoints
  MatchingSubsetOfGraph
  CoverHitsAllEdges
  SizeEquality

PROPERTIES
  ReachGoal
  InitialConditionOK

CHECK_DEADLOCK FALSE
</config>
Implement a general algorithm that performs the matching, not a custom based on the inputs.
*)

\* Fixed finite bipartite graph for this example
LeftNodes == {1, 2, 3}
RightNodes == {4, 5, 6}
Edges ==
  { <<1, 4>>, <<1, 5>>, <<2, 5>>, <<3, 6>> }

EdgeSet == LeftNodes \X RightNodes

(* --algorithm BipartiteMatching {

\* Implement maximum bipartite matching (and a minimum vertex cover certificate) here.

} *)
\* EVOLVE-BLOCK-END

\* Helpers
LeftOf(e)  == e[1]
RightOf(e) == e[2]

\* Sanity about the given graph
GraphOK ==
  /\ Edges \subseteq EdgeSet
  /\ IsFiniteSet(LeftNodes) /\ IsFiniteSet(RightNodes)

\* Invariants and properties over program variables
TypeOK ==
  /\ match \subseteq EdgeSet
  /\ coverLeft \subseteq LeftNodes
  /\ coverRight \subseteq RightNodes

\* Matching has no shared endpoints
NoSharedEndpoints ==
  /\ \A l \in LeftNodes:
       Cardinality({ r \in RightNodes : <<l, r>> \in match }) \leq 1
  /\ \A r \in RightNodes:
       Cardinality({ l \in LeftNodes : <<l, r>> \in match }) \leq 1

\* The matching must use only graph edges
MatchingSubsetOfGraph == match \subseteq Edges

\* Vertex cover checks
EdgeCovered(e) == LeftOf(e) \in coverLeft \/ RightOf(e) \in coverRight
CoverHitsMatchingEdges == \A e \in match: EdgeCovered(e)
CoverHitsAllEdges      == \A e \in Edges: EdgeCovered(e)

\* Size equality (Kőnig's theorem certificate)
SizeEquality == Cardinality(match) = Cardinality(coverLeft) + Cardinality(coverRight)

\* Initial condition sanity (optional)
InitialConditionOK ==
  Init => /\ match = {}
          /\ coverLeft = {}
          /\ coverRight = {}

\* Goal states: a valid certificate of optimality was found
ValidCertificate ==
  /\ NoSharedEndpoints
  /\ MatchingSubsetOfGraph
  /\ CoverHitsAllEdges
  /\ SizeEquality

ReachGoal == <>ValidCertificate

\* Encourage fairness in the synthesized Next
FairSpec == Spec /\ WF_vars(Next)

====