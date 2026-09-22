import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch02

/-! Generated numeric mask check for batch 2. -/
namespace AMEProbe.BinaryDirect.Batch02Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 2 + r.val).bitIndices.length = 5 →
      mask (Batch02.lookup (256 * 2 + r.val)).val = 256 * 2 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch02Coverage
#print axioms AMEProbe.BinaryDirect.Batch02Coverage.mask_correct
