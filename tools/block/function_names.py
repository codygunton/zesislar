"""Validate the name prefix shared by table and promotion renderers."""
from dataclasses import dataclass
import re


@dataclass(frozen=True)
class FunctionNames:
    prefix: str = "decodeItem"

    def __post_init__(self):
        if not isinstance(self.prefix, str) or not re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_']*", self.prefix):
            raise ValueError("The function prefix is not a Rocq identifier.")

    @property
    def module(self):
        return self.prefix[0].upper() + self.prefix[1:]

    @property
    def filename(self):
        return re.sub(r"(?<!^)(?=[A-Z])", "_", self.prefix).lower()

    @property
    def hints(self):
        return f"ZesuSsz.Compliance.{self.module}Hints"

    @property
    def table_module(self):
        return f"ZesuSsz.Generated.{self.module}.BlockTable"

    @property
    def proofs(self):
        return f"ZesuSsz.Proofs.{self.module}"

    @property
    def proof_directory(self):
        return self.proofs.replace(".", "/")

    def state(self, pc):
        return f"{self.prefix}State{pc:x}"

    @property
    def table(self):
        return self.prefix + "BlockTable"


def prefix_argument(value):
    """Accept either the inventory name or its final component."""
    prefix = value.rsplit(".", 1)[-1]
    FunctionNames(prefix)
    return prefix
