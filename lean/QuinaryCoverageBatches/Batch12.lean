import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch12

/-! Generated numeric mask check for batch 12. -/
namespace AMEProbe.QuinaryDirect.Batch12Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 12 + r.val).bitIndices.length = 6 →
      mask (Batch12.lookup (256 * 12 + r.val)).val = 256 * 12 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch12Coverage
#print axioms AMEProbe.QuinaryDirect.Batch12Coverage.mask_correct
