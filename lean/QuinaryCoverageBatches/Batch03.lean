import MaskEncoding
import QuinaryCoverage
import QuinaryDirectBatches.Batch03

/-! Generated numeric mask check for batch 3. -/
namespace AMEProbe.QuinaryDirect.Batch03Coverage
open AMEProbe.QuinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 3 + r.val).bitIndices.length = 6 →
      mask (Batch03.lookup (256 * 3 + r.val)).val = 256 * 3 + r.val := by
  decide +kernel

end AMEProbe.QuinaryDirect.Batch03Coverage
#print axioms AMEProbe.QuinaryDirect.Batch03Coverage.mask_correct
