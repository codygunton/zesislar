Require Import ZesuSsz.Automation2.PureFactProjection.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.

#[export] Instance decodeItemDomainAt_projection_head :
  ZesuPureFactHead decodeItemDomainAt := I.
#[export] Instance decodeItemC1BDomain_projection_head :
  ZesuPureFactHead decodeItemC1BDomain := I.
#[export] Instance decodeItemArgsWellFormed_projection_head :
  ZesuPureFactHead decodeItemArgsWellFormed := I.
#[export] Instance decodeItemEntryLayout_projection_head :
  ZesuPureFactHead ZesuSsz.Contracts.RlpDecodeItem.decodeItemEntryLayout := I.
