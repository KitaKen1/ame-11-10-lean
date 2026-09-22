import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch09

/-! Generated numeric mask check for batch 9. -/
namespace AMEProbe.QuinaryDirect.Batch09Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 9 + r.val).bitIndices.length = 6 →
      mask (Batch09.lookup (256 * 9 + r.val)).val = 256 * 9 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch09Coverage
#print axioms AMEProbe.QuinaryDirect.Batch09Coverage.mask_correct
