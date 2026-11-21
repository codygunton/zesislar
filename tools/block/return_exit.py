"""Function-return exits of a design table, return and entry facts, return-exit matching."""

from render_support import expression


def return_blocks(design):
    """Use the table's return clauses, never the absence of successors alone."""
    result = {}
    seen = set()
    for block in design["blocks"]:
        pc = int(block["entry_pc"], 0)
        if pc in seen:
            raise ValueError("The design repeats a block address.")
        seen.add(pc)
        successors = block["successor_pcs"]
        clause = block.get("return_clause")
        if clause is not None:
            if successors or "return_instruction_pc" not in clause:
                raise ValueError("The design has an inconsistent function-return exit.")
            result[pc] = block
        elif not successors:
            raise ValueError("A terminal block has no declared exit kind.")
    return result


RETURN_TAIL = " ∗ True)) ∗ K)%I"


def add_return_facts(source, facts):
    """Add pure exit facts after the last fact of the one return package body.

    The owned resources come first, so they fix the package existentials (for
    example the output bytes) before a fact about them is proved.
    """
    if not facts:
        return source
    for fact in facts:
        expression(fact, "return fact")
        if "⌜" in fact or "⌝" in fact:
            raise ValueError("A return fact must be a bare proposition.")
    if source.count(RETURN_TAIL) != 1:
        raise ValueError("The return package needs exactly one pure fact tail.")
    added = "".join(" ∗ ⌜" + fact + "⌝" for fact in facts)
    return source.replace(RETURN_TAIL, added + RETURN_TAIL)


ENTRY_TAIL = "⌝))%I"


def add_entry_facts(source, facts):
    """Add pure facts after the last fact of the one entry alternative in source."""
    if not facts:
        return source
    for fact in facts:
        expression(fact, "entry fact")
    if source.count(ENTRY_TAIL) != 1:
        raise ValueError("The entry needs exactly one pure fact tail.")
    added = "".join(" ∗ ⌜" + fact + "⌝" for fact in facts)
    return source.replace(ENTRY_TAIL, "⌝" + added + "))%I")


def match_return_exits(designs, exits):
    """Pair each function_return exit with the design row of its return instruction.

    Returns (pairs, unreached): every exit at a design's `return_instruction_pc`
    pairs with that design, in design order; a design that no exit reaches is
    unreached. An exit without a design row is refused."""
    pairs, unreached = [], []
    for design in designs:
        at = int(design["return_instruction_pc"], 0)
        rows = [row for row in exits if int(row["instruction_pc"], 0) == at]
        if not rows:
            unreached.append(design["return_instruction_pc"])
        pairs += [(design, row) for row in rows]
    if len(pairs) != len(exits):
        raise ValueError("A function_return exit has no return design.")
    return pairs, unreached


def return_block_slots(boundaries, exits):
    """The boundary of the block the exits leave from, when that block carries entry slots
    (a duplicated return join); None otherwise. Every exit of one return design leaves from
    one return block; several return blocks of one design carry no slots."""
    blocks = {row["block_pc"] for row in exits}
    if len(blocks) != 1:
        return None
    block = next((row for row in boundaries if row["pc"] == next(iter(blocks))), None)
    return block if block is not None and block.get("slots") else None


def exit_slot(block, exit):
    """The entry slot of the slot block `block` that the function_return exit continues from.

    The exit's path extends the path of the block alternative it continued from (the source
    pass appends the block's own decisions), from the same seed; exactly one alternative
    may match."""
    matches = [number for number, alternative in enumerate(block["alternatives"])
               if alternative["seed_pc"] == exit["seed_pc"]
               and exit["path"][:len(alternative["path"])] == alternative["path"]]
    if len(matches) != 1:
        raise ValueError("A function_return exit continues from %d alternatives of %s."
                         % (len(matches), block["pc"]))
    slot, = [index for index, row in enumerate(block["slots"]) if matches[0] in row["alternatives"]]
    return slot


def allows_exit_resources_only(design):
    """A return fact `True` (or JSON true) states no meaning: the exit resources only."""
    fact = design["return_fact"]
    return fact is True or str(fact).strip() == "True"
