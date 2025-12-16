--------------------------- MODULE DijkstraMutex ---------------------------


EXTENDS Integers

CONSTANT Proc 


\* Hardware-level operations constraint:
\* Only the following per-label hardware atomic operations on shared memory are allowed:
\*  1) READ (load): Observes shared state only. Examples: `await (COND);` where
\*     `COND` reads shared vars and performs no assignment; or a `with` that binds
\*     to local state without writing to shared state.
\*  2) WRITE (store): A single assignment to exactly one shared variable or element
\*     (e.g., `x := v;` or `a[i] := v;`).
\*  3) ATOMIC RMW (read-modify-write): A single conditional that reads and writes
\*     the same shared variable exactly once (CAS/test-and-set style), e.g.:
\*       `if (x = old) { x := new; } else { skip; };`
\*  4) CONTROL: Pure control transfer with no shared memory effects (e.g., `goto L;`
\*     or `skip;`). Condition evaluation may read but must not write.
\* Not allowed in a single label: combining an `await` and a write; writing multiple
\* shared variables; reading and writing different shared variables; or sequencing
\* multiple statements that cause more than one hardware operation.

\* EVOLVE-BLOCK-START
(* --algorithm Mutex 
 { variables ...
   \* Implement Dijkstra-style mutual exclusion (shared-memory mutex) here.
   process (P \in Proc)
     skip;
 } *)
 \* EVOLVE-BLOCK-END


InCriticalSection(i) == pc[i] = "CriticalSection"
InNonCriticalSection(i) == pc[i] = "NonCriticalSection"
TryingToEnterCriticalSection(i) == pc[i] = "TryingToEnter"

MutualExclusion == \A i, j \in Proc : 
                    (i # j) => ~ /\ InCriticalSection(i)
                                 /\ InCriticalSection(j)

LSpec == Init /\ [][Next]_vars 
          /\ \A self \in Proc: WF_vars((~InNonCriticalSection(self)) /\ P(self))

DeadlockFreedom == 
    \A i \in Proc : 
      TryingToEnterCriticalSection(i) ~> (\E j \in Proc : InCriticalSection(j))



=============================================================================
