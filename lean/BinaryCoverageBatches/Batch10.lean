import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch10

/-! Generated numeric mask check for batch 10. -/
namespace AMEProbe.BinaryDirect.Batch10Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 10 + r.val).bitIndices.length = 5 →
      mask (Batch10.lookup (256 * 10 + r.val)).val = 256 * 10 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch10Coverage
#print axioms AMEProbe.BinaryDirect.Batch10Coverage.mask_correct
