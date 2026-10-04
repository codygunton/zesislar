"""Stage the bounded EIP-4844 record-extraction experiment.

Run this only with the pinned reference and pinned Sail compiler checkouts.
The staged files live in an ignored build directory and do not replace the
reviewed rung-1/rung-2 snapshot.
"""

import argparse
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import time

from generate import EVM_REVISION, SAIL_REVISION, check_source, digest

COMPILER_SHA256 = '517d6d68de8947926a0950d59de544350bf3ec289153e6ba63c6cfd5a664e16b'
PLUGIN_SHA256 = '8052ba334e708171eb74a6946678984408ae2f548c50ef03fee3780c074c2468'

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--evm-source', type=Path, required=True)
parser.add_argument('--sail-source', type=Path, required=True)
parser.add_argument('--stage', type=Path, required=True)
parser.add_argument('--compiler-build', type=Path)
parser.add_argument('--build-dir', type=Path)
parser.add_argument('--switch', default='/home/cody/islaris')
parser.add_argument('--run', action='store_true')
parser.add_argument('--handoff', action='store_true')
args = parser.parse_args()
repo = Path(__file__).resolve().parents[3]
check_source(args.evm_source, EVM_REVISION)
check_source(args.sail_source, SAIL_REVISION)
source = args.evm_source.resolve() / 'sail'
stage = args.stage.resolve()
stage_parent = (repo / 'build/blob-experiment').resolve()
if stage == stage_parent or not stage.is_relative_to(stage_parent):
    parser.error('The stage must be a child of build/blob-experiment.')
shutil.rmtree(stage, ignore_errors=True)
shutil.copytree(source, stage / 'source')
shutil.copy(repo / 'ZesuSsz/EvmSail/Rlp/decoder.sail_project', stage / 'source/decoder.sail_project')
shutil.copytree(repo / 'ZesuSsz/EvmSail/Rlp/shim', stage / 'source/shim')
(stage / 'sail').mkdir()
(stage / 'sail/lib').symlink_to(args.sail_source.resolve() / 'lib', target_is_directory=True)
p = stage / 'source/lib/rlp/codecs/transactions.sail'
s = p.read_text()
head = s.index('function decode_blob_tx forall')
tail = s.index('/*! Decodes the payload fields of an EIP-7702 transaction. */', head)
body = s[head:tail]
old = '''    struct {
        tx_type = BlobTx,
        sender = sender,
        raw = tx,
        nonce = rlp_decode_u256(nonce_f),
        chain_id = rlp_decode_uint64(chain_f),
        gas_limit = rlp_decode_gas(gas_f),
        is_create = to_f.content_len == 0,
        recipient = recipient,
        value = rlp_decode_u256(value_f),
        input_src = tx_input_span(data_f),
        access_list = access_list,
        max_fee = rlp_decode_u256(mf_f),
        max_blob_fee = rlp_decode_u256(mbf_f),
        max_priority_fee = rlp_decode_u256(mp_f),
        authorizations = EMPTY_AUTHORIZATION_LIST_REF,
        blob_hashes = blob_hashes,
        pubkey = pubkey,
        signing_hash = signing_hash,
        sig_v = v,
        sig_r = rlp_decode_u256(r_f),
        sig_s = rlp_decode_u256(s_f),
    }'''
assert body.count(old) == 1
new = '''    blob_tx_record(
        sender, tx, rlp_decode_u256(nonce_f), rlp_decode_uint64(chain_f),
        rlp_decode_gas(gas_f), to_f.content_len == 0, recipient,
        rlp_decode_u256(value_f), tx_input_span(data_f), access_list,
        rlp_decode_u256(mf_f), rlp_decode_u256(mbf_f), rlp_decode_u256(mp_f),
        blob_hashes, pubkey, signing_hash, v,
        rlp_decode_u256(r_f), rlp_decode_u256(s_f))'''
body = body.replace(old, new)
helper = '''/* Stage-only extraction of the pure transaction record constructor. */
function blob_tx_record forall 'blob_limit, transaction_blob_limit_value('blob_limit). (
    sender : address, tx : TransactionInputSlice, nonce : word,
    chain_id : chain_identifier, gas_limit : transaction_gas,
    is_create : bool, recipient : address, value : word,
    input_src : TransactionInputSlice, access_list : AccessListRef,
    max_fee : word, max_blob_fee : word, max_priority_fee : word,
    blob_hashes : BlobHashesFields('blob_limit), pubkey : StatelessInputSlice,
    signing_hash : hash, v : word, sig_r : word, sig_s : word
) -> TransactionFields('blob_limit) = struct {
    tx_type = BlobTx, sender = sender, raw = tx, nonce = nonce,
    chain_id = chain_id, gas_limit = gas_limit, is_create = is_create,
    recipient = recipient, value = value, input_src = input_src,
    access_list = access_list, max_fee = max_fee, max_blob_fee = max_blob_fee,
    max_priority_fee = max_priority_fee,
    authorizations = EMPTY_AUTHORIZATION_LIST_REF,
    blob_hashes = blob_hashes, pubkey = pubkey, signing_hash = signing_hash,
    sig_v = v, sig_r = sig_r, sig_s = sig_s
}

'''
arguments = [item.strip() for item in new.split('blob_tx_record(', 1)[1]
             .rsplit(')', 1)[0].replace('\n', ' ').split(',')]
signature = helper.split(') -> TransactionFields', 1)[0].split('). (', 1)[1]
parameters = [item.strip().split(':')[0].strip()
              for item in signature.replace('\n', ' ').split(',')]
assert len(arguments) == len(parameters) == 19
mapping = dict(zip(parameters, arguments))

def record_fields(value):
    body = value.split('struct {', 1)[1].split('}', 1)[0]
    return dict(item.strip().split('=', 1)
                for item in body.replace('\n', ' ').split(',') if '=' in item)

original_fields = record_fields(old)
helper_fields = record_fields(helper)
assert list(original_fields) == list(helper_fields)
for field, expression in original_fields.items():
    helper_expression = helper_fields[field].strip()
    substituted = mapping.get(helper_expression, helper_expression)
    assert re.sub(r'\s+', '', substituted) == re.sub(r'\s+', '', expression)
assert parameters == [helper_fields[field].strip() for field in original_fields
                      if helper_fields[field].strip() in mapping]
s = s[:head] + helper + body + s[tail:]
assert s.replace(helper, '', 1).replace(new, old, 1) == p.read_text()
module_name = 'evm_blob'
if args.handoff:
    record_stage = s
    blob_start = s.index('function decode_blob_tx forall')
    walk_start = s.index('    let chain_f = rlp_decode_item(fields);', blob_start)
    walk_end = s.index('    let data_f = rlp_decode_item(fields);', walk_start)
    walk = s[walk_start:walk_end]
    assert walk.count('rlp_decode_item(') == walk.count('rlp_cursor_advance(') == 7
    handoff = '''/* Existential handoff after the first seven blob-transaction fields. */
type BlobTxAnyField = {
    'off 'full 'content, rlp_field_ref_valid('off, 'full, 'content).
    RlpFieldRef('off, 'full, 'content)
}

struct BlobTxPrefixFields(
    'chain_off : Int, 'chain_len : Int, 'chain_content : Int,
    'next_off : Int, 'next_len : Int
), rlp_field_ref_valid('chain_off, 'chain_len, 'chain_content)
   & source_valid_range('next_off, 'next_len)
   & 'chain_off <= 'next_off = {
    chain_f : RlpFieldRef('chain_off, 'chain_len, 'chain_content),
    nonce_f : BlobTxAnyField,
    mp_f : BlobTxAnyField,
    mf_f : BlobTxAnyField,
    gas_f : BlobTxAnyField,
    to_f : BlobTxAnyField,
    value_f : BlobTxAnyField,
    fields : RlpCursor('next_off, 'next_len),
}

type BlobTxPrefix = {
    'chain_off 'chain_len 'chain_content 'next_off 'next_len,
    rlp_field_ref_valid('chain_off, 'chain_len, 'chain_content)
    & source_valid_range('next_off, 'next_len)
    & 'chain_off <= 'next_off.
    BlobTxPrefixFields('chain_off, 'chain_len, 'chain_content, 'next_off, 'next_len)
}

function blob_tx_prefix_pack forall
    'chain_off 'chain_len 'chain_content 'next_off 'next_len,
    rlp_field_ref_valid('chain_off, 'chain_len, 'chain_content)
    & source_valid_range('next_off, 'next_len)
    & 'chain_off <= 'next_off. (
    chain_f : RlpFieldRef('chain_off, 'chain_len, 'chain_content),
    nonce_f : BlobTxAnyField, mp_f : BlobTxAnyField,
    mf_f : BlobTxAnyField, gas_f : BlobTxAnyField,
    to_f : BlobTxAnyField, value_f : BlobTxAnyField,
    fields : RlpCursor('next_off, 'next_len)
) -> BlobTxPrefixFields('chain_off, 'chain_len, 'chain_content, 'next_off, 'next_len) =
    struct {
        chain_f = chain_f, nonce_f = nonce_f, mp_f = mp_f, mf_f = mf_f,
        gas_f = gas_f, to_f = to_f, value_f = value_f, fields = fields
    }

function decode_blob_tx_prefix forall 'source_off 'source_len,
    source_valid_range('source_off, 'source_len). (
    fields : RlpCursor('source_off, 'source_len)
) -> BlobTxPrefix = {
''' + walk + '''    blob_tx_prefix_pack(chain_f, nonce_f, mp_f, mf_f,
                        gas_f, to_f, value_f, fields)
}

'''
    wrapper = '''    let prefix = decode_blob_tx_prefix(fields);
    let chain_f = prefix.chain_f;
    let nonce_f = prefix.nonce_f;
    let mp_f = prefix.mp_f;
    let mf_f = prefix.mf_f;
    let gas_f = prefix.gas_f;
    let to_f = prefix.to_f;
    let value_f = prefix.value_f;
    let fields = prefix.fields;
'''
    s = s[:blob_start] + handoff + s[blob_start:walk_start] + wrapper + s[walk_end:]
    assert s.replace(handoff, '', 1).replace(wrapper, walk, 1) == record_stage
    module_name = 'evm_blob_handoff'
p.write_text(s)
(stage / 'slice.commands').write_text(
    ':slice_roots decode_blob_tx initialize_registers\n:slice_keep_std\n:slice\n'
    ':recheck_types\n:rewrites coq\n:target coq, ' + module_name + '\n:quit\n')
print(stage)

if args.run:
    if args.compiler_build is None or args.build_dir is None:
        parser.error('--run requires --compiler-build and --build-dir.')
    compiler_build = args.compiler_build.resolve()
    build_dir = args.build_dir.resolve()
    if not build_dir.is_relative_to(repo / '_build/agents'):
        parser.error('The Dune build directory must be private to this agent.')
    compiler = compiler_build / 'default/src/bin/sail.exe'
    plugin = compiler_build / 'default/src/sail_coq_backend/sail_plugin_coq.cmxs'
    version = subprocess.check_output([str(compiler), '--version'], text=True)
    if (SAIL_REVISION not in version or digest(compiler) != COMPILER_SHA256
            or digest(plugin) != PLUGIN_SHA256):
        raise ValueError('The Sail compiler does not match the pin.')

    def bounded(name, command, *, env=None, stdin=None):
        started = time.monotonic()
        peak = 0
        reason = 'exit'
        with (stage / (name + '.log')).open('w') as log:
            process = subprocess.Popen(command, cwd=stage, env=env, stdin=stdin,
                                       stdout=log, stderr=subprocess.STDOUT)
            while process.poll() is None:
                try:
                    status = (Path('/proc') / str(process.pid) / 'status').read_text()
                    rss = next(int(line.split()[1]) for line in status.splitlines()
                               if line.startswith('VmRSS:'))
                    peak = max(peak, rss)
                except (FileNotFoundError, StopIteration):
                    pass
                elapsed = time.monotonic() - started
                if elapsed >= 60 or peak > 2 * 1024 * 1024:
                    reason = 'time_cap' if elapsed >= 60 else 'memory_cap'
                    process.kill()
                    break
                time.sleep(.1)
            process.wait()
        result = dict(name=name, reason=reason, exit=process.returncode,
                      seconds=round(time.monotonic() - started, 3),
                      peakRssKiB=max(peak, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss),
                      workers=1)
        (stage / (name + '.json')).write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result))
        return result

    env = os.environ.copy()
    env['SAIL_NO_PLUGINS'] = '1'
    env['SAIL_DIR'] = str(stage / 'sail')
    env['PATH'] = str(repo / 'bin') + os.pathsep + env['PATH']
    (stage / 'output').mkdir()
    with (stage / 'slice.commands').open() as commands:
        generated = bounded('generation', [
            str(compiler), '--plugin', str(plugin), '--coq-semantic-range-types',
            '--coq-undef-axioms', '--coq-output-dir', 'output', '--project',
            'source/decoder.sail_project', '--all-modules', '--interact-custom',
        ], env=env, stdin=commands)
    if generated['exit'] != 0 or generated['reason'] != 'exit':
        raise SystemExit('The bounded Sail generation failed.')
    text = (stage / 'generation.log').read_text()
    if 'Error:' in text or 'Type error' in text:
        raise SystemExit('Sail reported an error despite exit status zero.')
    if 'Definition decode_blob_tx' not in (stage / 'output' / (module_name + '.v')).read_text():
        raise SystemExit('Sail did not generate the blob decoder definition.')

    stdpp = build_dir / 'default/generated/sail-stdpp'
    if not (stdpp / 'Real.vo').is_file():
        raise SystemExit('Build generated/sail-stdpp/Real.vo in the private Dune directory first.')
    for name in (module_name + '_types.v', module_name + '.v'):
        result = bounded(name, [
            'opam', 'exec', '--switch=' + args.switch, '--', 'coqc',
            '-Q', str(stdpp), 'SailStdpp', '-Q', 'output', '', '-time',
            str(stage / 'output' / name),
        ])
        if result['exit'] != 0 or result['reason'] != 'exit':
            break
