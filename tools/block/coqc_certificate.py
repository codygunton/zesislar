"""Check the approved coqc native certificate without proof replay."""
import hashlib
from pathlib import Path


def matches(path, expected):
    return Path(path).is_file() and hashlib.sha256(Path(path).read_bytes()).hexdigest() == expected


def native_closed(evidence, rendered):
    """Missing diagnostic groups do not certify closure; native Qed does."""
    compiler = evidence.get('compiler') or {}
    artifact = compiler.get('compiled_object') or {}
    debts = evidence.get('inherited_debts')
    statement = rendered['source'].split('Lemma ' + rendered['lemma'], 1)[1].split('\nProof.\n', 1)[0]
    if ('instr_body ' + rendered['entry_pc'] not in statement or
            rendered.get('scope') != 'unproved native designed boundary' or
            evidence.get('original_source_sha256') != hashlib.sha256(rendered['source'].encode()).hexdigest() or
            evidence.get('statement_sha256') != rendered.get('statement_sha256') or
            evidence.get('entry_definition') != rendered.get('entry_definition') or
            evidence.get('successors') != rendered.get('successors')):
        return False
    if (not isinstance(debts, dict) or any(debts.values()) or
            not evidence.get('native_qed_compiled') or compiler.get('exit_code') != 0 or
            compiler.get('limit') or not evidence.get('primary_tactic_entered') or
            evidence.get('primary_tactic') != 'try zesu_block.' or
            evidence.get('primary_timeout') != 300 or
            evidence.get('assumption_verification', {}).get('verified') is not True or
            evidence['assumption_verification'].get('assumptions') != []):
        return False
    return all(matches(path, expected) for path, expected in (
        (evidence['source'], evidence['source_sha256']),
        (evidence['log'], evidence['log_sha256']),
        (artifact.get('path', ''), artifact.get('sha256'))))
