import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch13

/-! Generated numeric mask check for batch 13. -/
namespace AMEProbe.QuinaryDirect.Batch13Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 13 + r.val).bitIndices.length = 6 →
      mask (Batch13.lookup (256 * 13 + r.val)).val = 256 * 13 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch13Coverage
#print axioms AMEProbe.QuinaryDirect.Batch13Coverage.mask_correct
