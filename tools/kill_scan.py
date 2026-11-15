#!/usr/bin/env python3
"""Find process kills that can reach jobs the caller does not own.

In the omp bash tool `$$` is the shared harness PID, so every agent's
background jobs are its children. On 2026-11-15 one agent's kill by parent
PID ended the coordinator's watcher and the worker broker. A kill by process
name or by a pgrep match has the same reach. `run_registry.py launch`
refuses a command whose scripts contain such a kill, and the proof hygiene
check refuses one in a committed `tools/` script.

Usage: kill_scan.py PATH...   (exit 1 when a file contains an unsafe kill)
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

# Each pattern is split into string fragments, so this file passes its own scan.
PATTERNS = (
    (re.compile(r'(?<![\w.-])p' r'kill\b'), 'kill by process name or parent'),
    (re.compile(r'(?<![\w.-])kill' r'all\b'), 'kill by process name'),
    (re.compile(r'(?<![\w.-])kill\b[^\n;|&#]*(?:\$\(|`)\s*p' r'grep\b'), 'kill of a process-name match'),
    (re.compile(r'(?<![\w])-P\s*["\']?\$' r'\$'), 'match by parent PID of the shared shell'),
)
SAFE_FORM = ('Safe form: save the PID from $! at launch and kill only "$pid", or launch the job with '
             'tools/bg NAME CMD... and stop it with tools/run_registry.py stop <run id>.')
SCRIPT_SUFFIXES = ('.sh', '.bash', '.py')
MAX_SCRIPT_BYTES = 4 * 1024 * 1024
MAX_DEPTH = 4
MAX_FILES = 400
TOKEN = re.compile(r'[^\s\'"`;|&()<>=,\[\]{}]+')


@dataclass(frozen=True)
class Finding:
    source: str
    line: int
    text: str
    reason: str

    def message(self):
        return f'{self.source}:{self.line}: {self.text.strip()}: unsafe process kill ({self.reason}). {SAFE_FORM}'


def scan_text(text, source):
    """Return the unsafe kills on executable lines; comment lines do not run."""
    findings = []
    for number, line in enumerate(text.splitlines(), 1):
        if line.lstrip().startswith('#'):
            continue
        for pattern, reason in PATTERNS:
            if pattern.search(line):
                findings.append(Finding(source, number, line, reason))
                break
    return findings


def script_text(path):
    """Return the text of a script file, or None for anything else."""
    try:
        path = Path(path)
        if not path.is_file() or path.stat().st_size > MAX_SCRIPT_BYTES:
            return None
        data = path.read_bytes()
    except OSError:
        return None
    if b'\0' in data[:8192] or not (path.name.endswith(SCRIPT_SUFFIXES) or data.startswith(b'#!')):
        return None
    return data.decode('utf-8', errors='replace')


def referenced_paths(text, bases):
    """Existing files named by path-like tokens, resolved from each base directory.

    A token that starts with a variable (`$here/xrun.sh`, `"$(dirname "$0")"/q.sh`)
    keeps its literal tail, so queue scripts started beside a script are found.
    """
    found = []
    for line in text.splitlines():
        if line.lstrip().startswith('#'):
            continue
        for token in TOKEN.findall(line):
            if '$' in token:
                token = token.split('/')
                while token and ('$' in token[0] or not token[0]):
                    token = token[1:]
                token = '/'.join(token)
            if not token or not ('/' in token or token.endswith(SCRIPT_SUFFIXES)):
                continue
            candidate = Path(token)
            options = [candidate] if candidate.is_absolute() else [Path(base) / candidate for base in bases]
            for option in options:
                if option.is_file():
                    found.append(option.resolve())
                    break
    return found


def scan_command(command, cwd):
    """Scan a command line, the scripts it names, and the scripts those start."""
    cwd = Path(cwd)
    findings = scan_text('\n'.join(command), '<command line>')
    queue = [(path, 0) for path in referenced_paths('\n'.join(command), [cwd])]
    seen = set()
    while queue and len(seen) < MAX_FILES:
        path, depth = queue.pop(0)
        if path in seen:
            continue
        seen.add(path)
        text = script_text(path)
        if text is None:
            continue
        findings.extend(scan_text(text, str(path)))
        if depth < MAX_DEPTH:
            queue.extend((child, depth + 1) for child in referenced_paths(text, [path.parent, cwd]))
    return findings


def tree_failures(root, names):
    """Unsafe kills in the given repository-relative files under tools/."""
    failures = []
    for name in names:
        if not name.startswith('tools/'):
            continue
        text = script_text(Path(root) / name)
        if text is not None:
            failures.extend(finding.message() for finding in scan_text(text, name))
    return failures


def main(paths):
    findings = []
    for path in paths:
        text = script_text(path)
        if text is not None:
            findings.extend(scan_text(text, path))
    for finding in findings:
        print(finding.message())
    return 1 if findings else 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
