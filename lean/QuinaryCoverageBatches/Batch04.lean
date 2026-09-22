import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch04

/-! Generated numeric mask check for batch 4. -/
namespace AMEProbe.QuinaryDirect.Batch04Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 4 + r.val).bitIndices.length = 6 →
      mask (Batch04.lookup (256 * 4 + r.val)).val = 256 * 4 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch04Coverage
#print axioms AMEProbe.QuinaryDirect.Batch04Coverage.mask_correct
