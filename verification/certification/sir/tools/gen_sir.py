#!/usr/bin/env python3
"""Generate Challenge/Sir.lean from exact slices of the project sources."""
import os
import sys
# Repository root (this file is verification/certification/sir/tools/gen_sir.py).
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', '..')) + '/'
cache = {}


def src(mod, a, b=None):
    if b is None:
        b = a
    if mod not in cache:
        cache[mod] = open(ROOT + 'Freezing1/' + mod + '.lean').read().split('\n')
    return '\n'.join(cache[mod][a - 1:b])


out = []
import os
BLANK_AFTER = int(os.environ.get('BLANK_AFTER', '6'))


def emit(text=''):
    out.append(text)


def doc(text):
    emit('/-- ' + text.strip() + ' -/')


def block(header, items, footer, fake=None):
    """header: list of lines; items: list of strings (already text); footer line."""
    hdr = [h for h in header if h != '']
    if fake:
        emit('run_cmd Lean.modifyEnv (·.setMainModule `' + fake + ')')
    for h in hdr:
        emit(h)
    prev = None
    for it in items:
        if prev is not None:
            if prev.count('\n') + 1 >= BLANK_AFTER:
                emit()
        emit(it)
        prev = it
    emit(footer)
    emit()


def D(text, code):
    """docstring + code; a source docstring already present in the slice is kept"""
    if code.startswith('set_option ') and ' in\n' in code:
        pre, _, rest = code.partition(' in\n')
        return pre + ' in\n' + D(text, rest)
    if code.lstrip().startswith('/--'):
        return code
    t = ' '.join(text.split())
    if len('/-- ' + t + ' -/') <= 130:
        return '/-- ' + t + ' -/\n' + code
    return '/-- ' + text.strip() + ' -/\n' + code


def N(code):
    return code


exec(open(sys.argv[1]).read())

text = '\n'.join(out).rstrip('\n') + '\n'
open(sys.argv[2], 'w').write(text)
print('lines', text.count('\n'), 'bytes', len(text.encode()))
