import sys,os
sys.dont_write_bytecode=True
os.environ['PYTHONDONTWRITEBYTECODE']='1'
"""Inspect one explicit Python environment. Do not import a proof provider."""
import importlib
import importlib.metadata
import json
import locale
import os
from pathlib import Path
import sys
import sysconfig


def main():
    request = json.loads(sys.stdin.read())
    # Model the source directory of the future Python entry point.
    sys.path[0] = request['entry_directory']
    sys.path[1:1] = request['search_prefix']
    modules = []
    for name in request['modules']:
        module = importlib.import_module(name)
        origin = getattr(module, '__file__', None)
        if not origin:
            raise ValueError('A requested Python module has no source origin.')
        modules.append({'name': name, 'path': str(Path(origin).absolute())})
    distributions = []
    for distribution in sorted(importlib.metadata.distributions(),
                               key=lambda d: (d.metadata['Name'].lower(), d.version)):
        if distribution.files is None:
            raise ValueError('A Python distribution has no file inventory.')
        files = sorted({str(Path(distribution.locate_file(f)).absolute())
                        for f in distribution.files})
        distributions.append({'name': distribution.metadata['Name'],
                              'version': distribution.version, 'files': files})
    print(json.dumps({'executable': sys.executable, 'version': sys.version,
                     'version_short': sys.version.split()[0],
                     'hash_randomization': sys.flags.hash_randomization,
                     'environment': dict(os.environ),
                     'locale': {name: locale.setlocale(getattr(locale, name))
                                for name in ['LC_CTYPE', 'LC_NUMERIC', 'LC_TIME',
                                             'LC_COLLATE', 'LC_MONETARY']},
                     'sys_path': sys.path, 'sysconfig': sysconfig.get_paths(),
                     'modules': modules, 'distributions': distributions}))


if __name__ == '__main__':
    main()
