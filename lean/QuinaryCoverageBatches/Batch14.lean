import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch14

/-! Generated numeric mask check for batch 14. -/
namespace AMEProbe.QuinaryDirect.Batch14Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 14 + r.val).bitIndices.length = 6 →
      mask (Batch14.lookup (256 * 14 + r.val)).val = 256 * 14 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch14Coverage
#print axioms AMEProbe.QuinaryDirect.Batch14Coverage.mask_correct
