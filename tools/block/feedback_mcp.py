#!/usr/bin/env python3
"""Store complete feedback without changing the pinned SDK response."""
import hashlib
import json
import os
from pathlib import Path


def save_feedback(state, displayed, directory, include_warnings=True):
    messages = [message for level, message in (state.feedback or [])
                if message and (include_warnings or level != 2)]
    if not messages or displayed is None:
        return
    raw = '\n'.join(messages)
    key = hashlib.sha256(displayed.encode()).hexdigest()
    payload = {'display_sha256': key, 'raw_sha256': hashlib.sha256(raw.encode()).hexdigest(),
               'raw': raw, 'include_warnings': include_warnings}
    path = Path(directory)/f'{key}.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True) + '\n'
    if path.exists() and path.read_text() != text:
        raise ValueError('The feedback export changed for the same display hash')
    path.write_text(text)


def install_exporter(interactive, directory):
    """Keep SDK responses unchanged and store the complete feedback separately."""
    original = interactive._extract_feedback
    def export(state, *, include_warnings=True):
        displayed = original(state, include_warnings=include_warnings)
        save_feedback(state, displayed, directory, include_warnings)
        return displayed
    interactive._extract_feedback = export


def main():
    from rocq_mcp import server
    from rocq_mcp import interactive
    install_exporter(interactive, os.environ['ZESU_FEEDBACK_DIR'])
    server.main()


if __name__ == '__main__':
    main()
