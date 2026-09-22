import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch03

/-! Generated numeric mask check for batch 3. -/
namespace AMEProbe.BinaryDirect.Batch03Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 3 + r.val).bitIndices.length = 5 →
      mask (Batch03.lookup (256 * 3 + r.val)).val = 256 * 3 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch03Coverage
#print axioms AMEProbe.BinaryDirect.Batch03Coverage.mask_correct
