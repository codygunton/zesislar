"""Identify only regenerated runtime outputs. Keep proof inputs bound."""
from pathlib import PurePath


def excluded(path):
    path = PurePath(path)
    return ('__pycache__' in path.parts or path.suffix == '.pyc'
            or path.name in {'.lia.cache', '.nia.cache'}
            or ('_build' in path.parts and path.name in {'log', 'trace.csexp'}))


def python_argv(argv):
    """Disable writes for each explicitly selected Python interpreter."""
    result = []
    for index, word in enumerate(argv):
        result.append(word)
        if PurePath(word).name in {'python', 'python3', 'python3.12'} and (index + 1 == len(argv) or argv[index + 1] != '-B'):
            result.append('-B')
    return result
