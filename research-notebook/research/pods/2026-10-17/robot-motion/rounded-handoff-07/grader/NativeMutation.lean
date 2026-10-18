import NativeData
namespace IndependentNativeDataReview
open NativeRational
def changedJoin : List Piece := match hold_jitter__ruckig with
  | s::t::rest => s::{t with p := t.p+1/1000}::rest
  | xs => xs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem changed_join_is_rejected : check (5/2) changedJoin = false := by decide +kernel
end IndependentNativeDataReview
