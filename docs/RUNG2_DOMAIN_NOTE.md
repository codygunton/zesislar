# Rung-2 nested-header audit

The proved example `fittingOuterHeader` has a fitting outer list and a child header that wraps a 64-bit length sum. The user selected C1-B. The public rung-2 domain does not narrow to `headerFits`.

`allContiguousHeadersFit` is a candidate narrower domain. Let `fieldSlices(bytes)` be a pure cursor walk over the outer list payload. The walk follows the selected parent-header field schedule. It records the remaining slice before each of the 17 direct `decodeItem` sites and three `nextUint64` child calls. On a successful item, it advances by that item's full length. It requires a positive consumed length within the remaining slice. It stops at the first rejected item. The proposed condition is:

```text
allContiguousHeadersFit(bytes) :=
  headerFits(bytes) and
  every slice in fieldSlices(bytes) satisfies headerFits.
```

This condition excludes an input when a reached child has an overflowing long-length header, even if its outer list header fits. It does not exclude every malformed child. A truncated length header can satisfy `headerFits` and still reject. The walk must record only reached calls; checking arbitrary byte positions would narrow the domain without a decoder reason.

Sail's slice and cursor checks keep each read inside its backing bytes. They do not imply `headerFits` for every binary child call from the outer condition. A successful Sail `rlp_decode_item` also checks that the full length is positive and fits the remaining cursor. Sail rejection gives no such precondition for the binary call. The same-slice correspondence remains a machine proof obligation. The known-bug relation applies to each reached nested wrap.

The candidate domain would narrow the public rung-2 claim, so it is not a public target. `nestedWrapOccurs` uses the reached-slice walk only to identify the known-bug trigger. A machine proof must connect each actual call to that walk.

Q29 found that this condition still includes field-boundary truncations that Sail accepts. Selected ELF guards reject several missing required fields by static analysis. The [pinned vectors](../ZesuSsz/Evidence/PARENT_HEADER_VECTORS.json) record the mismatch. Rung-2 rejection agreement stays separate while the user decides this class.
