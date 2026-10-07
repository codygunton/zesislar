"""Bind a frozen launcher to its own input and output directory."""
import json
from pathlib import Path


def load_inputs(launcher, index, output):
    """Reject an index or output directory from another attempt before writes."""
    attempt = Path(launcher).resolve().parent
    index = Path(index).resolve()
    output = Path(output).resolve()
    if index.parent != attempt:
        raise ValueError("The input index belongs to another attempt")
    if output != attempt:
        raise ValueError("The output directory belongs to another attempt")
    data = json.loads(index.read_text())
    if Path(data["attempt_directory"]).resolve() != attempt:
        raise ValueError("The input index binds another attempt directory")
    return data
