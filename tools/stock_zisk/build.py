#!/usr/bin/env python3
"""Build unchanged stock zesu through the upstream ZisK guest recipe.

The caller first builds the pinned ZisK static library with its custom
Rust toolchain. The author linker script remains byte-identical.
Only the missing stock exit ABI and build staging differ from upstream.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

PINS = {
    'zesu': 'd8071c422f0faf2c52d85b401192fdffc31fd5ac',
    'zisk': 'fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3',
    'guest': 'be591e90ecbd94b0a3185809ba5ed74268558fa3',
}
HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_pin(path, expected):
    actual = subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
    if actual != expected:
        raise ValueError(f'Wrong source pin: {path}: {actual}')
    for arguments in [['diff','--exit-code'],['diff','--cached','--exit-code']]:
        subprocess.run(['git','-C',str(path),*arguments],check=True)
    return {'commit': actual, 'tracked_sources_unchanged': True}


def build(args):
    sources = {name: source_pin(getattr(args,name),pin) for name,pin in PINS.items()}
    if subprocess.check_output(['zig','version'],text=True).strip() != '0.16.0':
        raise ValueError('Zig 0.16.0 is required')
    args.build_dir.mkdir(parents=True,exist_ok=True)
    global_cache=args.build_dir/'zig-global'
    object_command=['zig','build','rv64im-object','-Doptimize=ReleaseFast',f'-j{args.jobs}',
        '--cache-dir',str(args.build_dir/'zig-local'),'--global-cache-dir',str(global_cache)]
    subprocess.run(object_command,cwd=args.zesu,check=True)
    stage=args.build_dir/'guest';stage.mkdir(exist_ok=True)
    (stage/'src').mkdir(exist_ok=True);(stage/'lib').mkdir(exist_ok=True)
    upstream=args.guest/'zisk'
    for name in ['build.zig','build.zig.zon','Makefile']:
        shutil.copyfile(upstream/name,stage/name)
    (stage/'src/zisk_host.zig').write_bytes((upstream/'src/zisk_host.zig').read_bytes()
                                        +(HERE/'exit.zig').read_bytes())
    linker=upstream/'zisk.ld'
    shutil.copyfile(linker,stage/'zisk.ld')
    shutil.copyfile(args.runtime_library,stage/'lib/libziskos_staticlib.a')
    link_command=['zig','build','-Doptimize=ReleaseFast',f'-Dzesu_obj={args.zesu}/zig-out/lib/zesu.o',
        f'-j{args.jobs}','--global-cache-dir',str(global_cache)]
    subprocess.run(link_command,cwd=stage,check=True)
    args.out.mkdir(parents=True,exist_ok=True)
    elf=args.out/'zesu-zisk.elf'
    shutil.copyfile(stage/'zig-out/bin/zesu-zisk',elf)
    for name,command in [('disassembly.objdump',['riscv64-elf-objdump','-d']),
                         ('symbols.txt',['riscv64-elf-readelf','-Ws']),
                         ('elf-layout.txt',['riscv64-elf-readelf','-h','-l','-S'])]:
        with (args.out/name).open('w') as output:
            subprocess.run([*command,str(elf)],stdout=output,check=True)
        artifact=args.out/name
        artifact.write_text("".join(line.rstrip()+"\n" for line in artifact.read_text().splitlines()))
    record={'sources':sources,'zig_version':'0.16.0','jobs':args.jobs,
        'object_command':object_command,'link_command':link_command,
        'linker_script_sha256':digest(linker),'runtime_library_sha256':digest(args.runtime_library),
        'stock_object_sha256':digest(args.zesu/'zig-out/lib/zesu.o'),
        'elf_sha256':digest(elf),'adapters':{name:digest(HERE/name) for name in ['exit.zig']}}
    (args.out/'build-recipe.json').write_text(json.dumps(record,indent=2)+'\n')
    return record


def main():
    parser=argparse.ArgumentParser()
    for name in PINS:
        parser.add_argument('--'+name,type=lambda value:Path(value).resolve(),required=True)
    parser.add_argument('--runtime-library',type=lambda value:Path(value).resolve(),required=True)
    parser.add_argument('--build-dir',type=lambda value:Path(value).resolve(),required=True)
    parser.add_argument('--out',type=lambda value:Path(value).resolve(),required=True)
    parser.add_argument('--jobs',type=int,default=8)
    args=parser.parse_args()
    if not 1<=args.jobs<=48:parser.error('jobs must be between 1 and 48')
    build(args)


if __name__=='__main__':main()
