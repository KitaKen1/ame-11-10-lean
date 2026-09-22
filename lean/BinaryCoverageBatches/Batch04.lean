import MaskEncoding
import BinaryCoverage
import BinaryDirectBatches.Batch04

/-! Generated numeric mask check for batch 4. -/
namespace AMEProbe.BinaryDirect.Batch04Coverage
open AMEProbe.BinaryDirect
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

theorem mask_correct : ∀ r : Fin 256,
    (256 * 4 + r.val).bitIndices.length = 5 →
      mask (Batch04.lookup (256 * 4 + r.val)).val = 256 * 4 + r.val := by
  decide +kernel

end AMEProbe.BinaryDirect.Batch04Coverage
#print axioms AMEProbe.BinaryDirect.Batch04Coverage.mask_correct
