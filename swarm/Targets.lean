import RankTwoTargets
import RankTwoCertificate

/-!
# The objects the frozen statements are about

The definitions live in `RankTwoTargets.lean` at the repository root, so that this file and
`RankTwoClassification.lean` share one copy of `cartan`, `titsForm` and `titsBilin` instead of two
that can drift. This module re-exports them together with the reflection model of
`RankTwoCertificate` (`V`, `s1`, `s2`, `step`, `iter`, `HasExactPeriod`), which is everything a
submission needs:

```
import Targets
namespace OperatorFirst.CoxeterRankTwo
...
```
-/
