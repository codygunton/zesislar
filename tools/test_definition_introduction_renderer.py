"""Include the declaration renderer controls in the stock test discovery."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent / "block"))

from test_definition_introduction import DefinitionIntroduction
