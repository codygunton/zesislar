#!/usr/bin/env python3
"""Build unchanged stock zesu through the upstream ZisK guest recipe.

The caller first builds the pinned ZisK static library with its custom
Rust toolchain. The author linker script remains byte-identical.
Build staging preserves the upstream guest host without an exit adapter.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

import manifest

PINS = {
    'zesu': 'b5483dda21d72405c50a22cb6406a1231e51a579',
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


def measured_run(command, cwd, jobs):
    start = time.monotonic()
    process = subprocess.Popen(command, cwd=cwd)
    _, status, usage = os.wait4(process.pid, 0)
    process.returncode = os.waitstatus_to_exitcode(status)
    measurement = {'elapsed_seconds': round(time.monotonic()-start, 3),
        'peak_rss_kib': usage.ru_maxrss, 'workers': jobs,
        'exit_code': process.returncode}
    print(json.dumps({'command': command, 'measurement': measurement}), flush=True)
    if process.returncode:
        raise subprocess.CalledProcessError(process.returncode, command)
    return measurement


def build(args):
    previous_path = args.runtime_build_recipe or args.out/'build-recipe.json'
    previous = json.loads(previous_path.read_text())
    # The runtime is a separate build. Require its recorded compiler identities.
    for name in ['rustc', 'cargo', 'cargo-zisk']:
        record = previous['inputs']['compiler/'+name]
        if digest(Path(record['path'])) != record['sha256']:
            raise ValueError(f'Changed runtime compiler: {name}')
    sources = {name: source_pin(getattr(args,name),pin) for name,pin in PINS.items()}
    if subprocess.check_output(['zig','version'],text=True).strip() != '0.16.0':
        raise ValueError('Zig 0.16.0 is required')
    args.build_dir.mkdir(parents=True,exist_ok=True)
    global_cache=args.build_dir/'zig-global'
    object_command=['zig','build','rv64im-object','-Doptimize=ReleaseFast',f'-j{args.jobs}',
        '--cache-dir',str(args.build_dir/'zig-local'),'--global-cache-dir',str(global_cache)]
    object_measurement = measured_run(object_command,args.zesu,args.jobs)
    stage=args.build_dir/'guest';stage.mkdir(exist_ok=True)
    (stage/'src').mkdir(exist_ok=True);(stage/'lib').mkdir(exist_ok=True)
    upstream=args.guest/'zisk'
    for name in ['build.zig','build.zig.zon','Makefile']:
        shutil.copyfile(upstream/name,stage/name)
    shutil.copyfile(upstream/'src/zisk_host.zig',stage/'src/zisk_host.zig')
    linker=upstream/'zisk.ld'
    shutil.copyfile(linker,stage/'zisk.ld')
    shutil.copyfile(args.runtime_library,stage/'lib/libziskos_staticlib.a')
    link_command=['zig','build','-Doptimize=ReleaseFast',f'-Dzesu_obj={args.zesu}/zig-out/lib/zesu.o',
        f'-j{args.jobs}','--global-cache-dir',str(global_cache)]
    link_measurement = measured_run(link_command,stage,args.jobs)
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
        'description': "stock zesu built with the authors' recipe at a different zesu revision",
        'zig_executable':str(Path(shutil.which('zig')).resolve()),
        'zig_executable_sha256':digest(Path(shutil.which('zig')).resolve()),
        'object_command':object_command,'link_command':link_command,
        'linker_script_sha256':digest(linker),'runtime_library_sha256':digest(args.runtime_library),
        'stock_object_sha256':digest(args.zesu/'zig-out/lib/zesu.o'),
        'elf_sha256':digest(elf),'adapters':{},
        'link_without_exit_adapter':{'passed':True,'host_sha256':digest(stage/'src/zisk_host.zig')},
        'measurements':{'object':object_measurement,'link':link_measurement},
        **{key:previous[key] for key in ['preserved_inputs','preservation_measurement'] if key in previous}}
    (args.out/'build-recipe.json').write_text(json.dumps(record,indent=2)+'\n')
    if not (args.out/'PROVENANCE.md').exists():
        (args.out/'PROVENANCE.md').write_text('# Stock zesu on ZisK\n\n'+record['description']+'.\n'
            'The build-recipe.json file records the checked inputs, commands, hashes, and measurements.\n'
            'No release-ELF comparison or machine-code proof accompanies this build.\n')
    manifest.record_build(args, record, previous)
    return record


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    for name in PINS:
        parser.add_argument('--'+name,type=lambda value:Path(value).resolve())
    parser.add_argument('--runtime-library',type=lambda value:Path(value).resolve())
    parser.add_argument('--runtime-build-recipe',type=lambda value:Path(value).resolve())
    parser.add_argument('--build-dir',type=lambda value:Path(value).resolve())
    parser.add_argument('--out',type=lambda value:Path(value).resolve(),required=True)
    parser.add_argument('--jobs',type=int,default=8)
    args=parser.parse_args()
    if args.check:
        manifest.check(args.out, PINS)
        return
    for name in [*PINS,'runtime_library','build_dir']:
        if getattr(args,name) is None:parser.error('--'+name.replace('_','-')+' is required for a build')
    if not 1<=args.jobs<=48:parser.error('jobs must be between 1 and 48')
    build(args)


if __name__=='__main__':main()
