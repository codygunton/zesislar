"""Restrict held-out observations without discarding private evidence."""
HELD_OUT=frozenset()  # All 16 pilot blocks are development blocks.

def selected(block):
 return str(block).lower().removeprefix('0x') in HELD_OUT

def summary(block,result,rule_hashes=()):
 if not selected(block):return result
 return {'block':str(block).lower().removeprefix('0x'),'held_out':True,
         'group_counts':result.get('group_counts'),'CPU':result.get('CPU'),
         'aggregate_peak_bytes':result.get('aggregate_peak_bytes'),
         'closure':result.get('closure'),'release':result.get('release'),
         'frozen_rule_hashes':list(rule_hashes)}
