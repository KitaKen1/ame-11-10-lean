import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch07

/-! Generated numeric mask check for batch 7. -/
namespace AMEProbe.QuinaryDirect.Batch07Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 7 + r.val).bitIndices.length = 6 →
      mask (Batch07.lookup (256 * 7 + r.val)).val = 256 * 7 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch07Coverage
#print axioms AMEProbe.QuinaryDirect.Batch07Coverage.mask_correct
