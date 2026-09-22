import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch14

/-! Generated numeric mask check for batch 14. -/
namespace AMEProbe.BinaryDirect.Batch14Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 14 + r.val).bitIndices.length = 5 →
      mask (Batch14.lookup (256 * 14 + r.val)).val = 256 * 14 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch14Coverage
#print axioms AMEProbe.BinaryDirect.Batch14Coverage.mask_correct
