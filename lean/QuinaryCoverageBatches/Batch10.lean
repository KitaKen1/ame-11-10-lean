import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch10

/-! Generated numeric mask check for batch 10. -/
namespace AMEProbe.QuinaryDirect.Batch10Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 10 + r.val).bitIndices.length = 6 →
      mask (Batch10.lookup (256 * 10 + r.val)).val = 256 * 10 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch10Coverage
#print axioms AMEProbe.QuinaryDirect.Batch10Coverage.mask_correct
