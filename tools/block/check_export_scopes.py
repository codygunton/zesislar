"""Reject scopes that exported automation and generated libraries can leak."""
from pathlib import Path
from tools.block.check_data_only_lemmas import rocq_commands


def violations(root):
    errors = []
    for directory in ('ZesuSsz/Automation', 'ZesuSsz/Generated'):
        for path in sorted((Path(root) / directory).rglob('*.v')):
            for command in rocq_commands(path.read_text()):
                words = [word for word, _ in command]
                if 'Open' in words and 'Scope' in words and 'Local' not in words:
                    errors.append(str(path) + ': Use Local Open Scope in an exported library.')
    return errors


def main():
    errors = violations(Path(__file__).resolve().parents[2])
    for error in errors:
        print(error)
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
