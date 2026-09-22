import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch01

/-! Generated numeric mask check for batch 1. -/
namespace AMEProbe.QuinaryDirect.Batch01Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 1 + r.val).bitIndices.length = 6 →
      mask (Batch01.lookup (256 * 1 + r.val)).val = 256 * 1 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch01Coverage
#print axioms AMEProbe.QuinaryDirect.Batch01Coverage.mask_correct
