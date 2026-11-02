"""Give arithmetic in a source-typed Z address its explicit notation scope."""
import re

try:
    from .entry_seed import _code_mask
except ImportError:
    from entry_seed import _code_mask


def z_address_scope(term):
    """Preserve the complete inner term. Do not scope a length or register."""
    if re.search(r'[-+*/]', _code_mask(term)):
        return '(' + term + ')%Z'
    return term
