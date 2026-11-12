"""Split raw-entry initialization from pre-TAG boundaries without moving a TAG."""
from dataclasses import replace


def split_at_cutpoints(blocks, cutpoints):
    cuts = set(cutpoints)
    instructions = [i for b in blocks for i in b.instructions]
    addresses = {i.addr for i in instructions}
    if len(addresses) != len(instructions):
        raise ValueError("overlapping x86 blocks/instructions")
    if not cuts <= addresses:
        raise ValueError("cutpoint is not an instruction boundary")
    result = []
    for block in blocks:
        if not block.instructions or block.start_addr != block.instructions[0].addr:
            raise ValueError("invalid x86 block partition")
        chunks = []
        for insn in block.instructions:
            if chunks and insn.addr != chunks[-1][-1].addr + chunks[-1][-1].size:
                raise ValueError("instruction gap inside x86 block")
            if not chunks or insn.addr in cuts:
                chunks.append([])
            chunks[-1].append(insn)
        for chunk in chunks:
            result.append(replace(block, start_addr=chunk[0].addr,
                                  end_addr=chunk[-1].addr + chunk[-1].size,
                                  instructions=list(chunk)))
    return result
