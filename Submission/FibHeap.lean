import Submission.FibHeapAccounting
import Submission.FibHeapForest
import Submission.FibHeapDynamic
import Submission.FibHeapRefine
import Submission.FibHeapAcyclic
import Submission.FibHeapSupport
import Submission.FibHeapSupportSet
import Submission.FibHeapLink
import Submission.FibHeapLinkWalk
import Submission.FibHeapCut
import Submission.FibHeapMerge
import Submission.FibHeapPromote
import Submission.FibHeapCascade
import Submission.FibHeapExtractMin
import Submission.FibHeapWitness

/-!
# The Fibonacci-heap program family

One umbrella for the machine-level Fibonacci heap: the encoding (`FibHeapRefine`
and below), the invariant bundle, the four array-level updaters — link
(`FibHeapLink`/`FibHeapLinkWalk`), cut (`FibHeapCut`), consolidation merge
(`FibHeapMerge`), promote (`FibHeapPromote`) — the decrease-key cascade
with its verified output witness (`FibHeapCascade`), and extract-min with its
splice, consolidation fold, and rank-cap output capstone
(`FibHeapExtractMin`).  `FibHeapWitness` holds the shape lemmas consumed by the
support-level abstraction.

Importing this module compiles the whole closure; the lib-root build is the
receipt of record for the family.
-/
