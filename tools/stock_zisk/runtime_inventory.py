"""Record allocator and memcpy boundaries from the selected ELF and source."""
import argparse
import json
from pathlib import Path

from elftools.elf.elffile import ELFFile

from closure import Image
import manifest


def symbol_record(image, name):
    symbol = image.symbols[name]
    return {'name': name, 'address': symbol['st_value'], 'size': symbol['st_size'],
            'type': symbol['st_info']['type']}


def record(image, recipe, source):
    vtable = symbol_record(image, 'alt_fl_alloc.vtable')
    if vtable['size'] != 32:
        raise ValueError('The allocator vtable does not contain four RV64 pointers')
    vtable['bytes'] = image.read(vtable['address'], vtable['size']).hex()
    slots = []
    for index, name in enumerate(['alloc', 'resize', 'remap', 'free']):
        address = int.from_bytes(image.read(vtable['address'] + index * 8, 8), 'little')
        entry = symbol_record(image, 'alt_fl_alloc.' + name)
        if entry['address'] != address:
            raise ValueError(f'The vtable {name} slot differs from its ELF symbol')
        entry.update(offset=index * 8, entry_bytes=image.read(address, 4).hex())
        slots.append(entry)
    vtable['slots'] = slots
    state = symbol_record(image, 'alt_fl_alloc.state')
    lists = symbol_record(image, 'alt_fl_alloc.free_lists')
    if state['size'] != 1 or lists['size'] != 22 * 8:
        raise ValueError('The allocator state size differs from the selected source')
    for item in [state, lists]:
        section = image.elf.get_section(image.symbols[item['name']]['st_shndx'])
        if section['sh_type'] != 'SHT_NOBITS':
            raise ValueError('The allocator state does not use ELF zero initialization')
        item.update(section=section.name, initialization='ELF NOBITS zero initialization; not a decoder-entry invariant')
    lists.update(word_bytes=8, class_count=22, initial_heads=[0] * 22)
    heap = {}
    for name in ['ZKVM_HEAP_POS', 'ZKVM_HEAP_TOP']:
        item = symbol_record(image, name)
        item['word_bytes'] = 8
        item['bytes'] = image.read(item['address'], 8).hex()
        item['initial_value'] = int.from_bytes(bytes.fromhex(item['bytes']), 'little')
        heap[name] = item
    for name in ['__zesu_heap_bottom', '__zesu_heap_top']:
        heap[name] = symbol_record(image, name)
    if heap['ZKVM_HEAP_POS']['initial_value'] != heap['__zesu_heap_bottom']['address']:
        raise ValueError('The initial heap position differs from the heap-bottom symbol')
    if heap['ZKVM_HEAP_TOP']['initial_value'] != heap['__zesu_heap_top']['address']:
        raise ValueError('The initial heap limit differs from the heap-top symbol')
    memcpy = symbol_record(image, 'memcpy')
    memcpy['bytes'] = image.read(memcpy['address'], memcpy['size']).hex()
    if bytes.fromhex(memcpy['bytes']) != bytes.fromhex('73a035813300c50067800000'):
        raise ValueError('The memcpy marker/add/return bytes differ from the selected service pattern')
    memcpy.update(csr=0x813, destination_register='x10', source_register='x11',
        length_register='x12', return_register='x1', extra_params_address=0xa0400f00,
        integer_register_clobbers=[], overlap='permitted; source snapshot follows the scratch count store',
        source_boundary='one complete populated readable section; scalar input zero fallback does not apply',
        observable_effect='no public service event; memory changes include the scratch word and destination',
        status='Statement only. No service correctness or termination proof.')
    zisk = Path(recipe['sources']['zisk']['path'])
    evidence = {name: manifest.file_record(zisk / name) for name in [
        'ziskos/entrypoint/src/dma/memcpy.s',
        'transpilers/riscv/src/riscv2zisk_context.rs',
        'core/src/operations/dma_memcpy.rs', 'core/src/mem.rs',
        'core/src/zisk_inst_builder.rs']}
    return {'schema': 1, 'artifact_identity': recipe['artifact_identity'],
        'elf_sha256': recipe['elf_sha256'], 'source': manifest.file_record(source),
        'runtime_source_evidence': evidence,
        'evidence_class': 'Static ELF and source analysis. No selected-ELF execution or proof.',
        'allocator_vtable': vtable, 'allocator_state': state, 'free_lists': lists,
        'heap_words': heap, 'memcpy': memcpy,
        'proof_obligations': [
            'Relate decoder-entry allocator state to initialization and prior calls.',
            'Preserve free-list ownership and live allocation disjointness.',
            'Establish heap capacity and arithmetic bounds for allocations.',
            'Record the exact named service premise in the rung-2 trust text.']}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    recipe = json.loads(args.manifest.read_text())
    elf = args.manifest.parent / 'zesu-zisk.elf'
    if manifest.digest(elf) != recipe['elf_sha256']:
        raise ValueError('The ELF differs from the manifest')
    if manifest.artifact_identity(recipe) != recipe['artifact_identity']:
        raise ValueError('The manifest input identity is stale')
    source = Path(recipe['sources']['zesu']['path']) / 'src/zkvm/alt_fl_alloc.zig'
    with elf.open('rb') as stream:
        result = record(Image(ELFFile(stream)), recipe, source)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print('Recorded four allocator slots, 22 free lists, two heap words, and the memcpy boundary.')


if __name__ == '__main__':
    main()
