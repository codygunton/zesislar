# Rung-2 nested-header domain for review

The current public input condition, `headerFits`, checks the outer RLP item. It does not establish that each child item meets C1-A. The proved example `fittingOuterHeader` has a fitting outer list and a child header that would wrap a 64-bit length sum.

`allContiguousHeadersFit` is a candidate narrower domain. Let `fieldSlices(bytes)` be a pure cursor walk over the outer list payload. The walk follows the selected parent-header field schedule. It records the remaining slice before each of the 17 direct `decodeItem` sites and three `nextUint64` child calls. On a successful item, it advances by that item's full length. It requires a positive consumed length within the remaining slice. It stops at the first rejected item. The proposed condition is:

```text
allContiguousHeadersFit(bytes) :=
  headerFits(bytes) and
  every slice in fieldSlices(bytes) satisfies headerFits.
```

This condition excludes an input when a reached child has an overflowing long-length header, even if its outer list header fits. It does not exclude every malformed child. A truncated length header can satisfy `headerFits` and still reject. The walk must record only reached calls; checking arbitrary byte positions would narrow the domain without a decoder reason.

Sail's slice and cursor checks keep each read inside its backing bytes. They do not imply `headerFits` for every binary child call from the outer condition. A successful Sail `rlp_decode_item` also checks that the full length is positive and fits the remaining cursor. That success can support the child condition after a proof connects Sail's cursor to the same binary call. Sail rejection gives no such precondition for the binary call. The same-slice correspondence and each nested C1-A fact remain explicit composition obligations.

The candidate domain would narrow the public rung-2 claim. The current proof plan keeps the outer domain and the nested obligations separate until the user reviews this choice.
