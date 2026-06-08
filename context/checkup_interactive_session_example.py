from pathlib import Path
import sys


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.checkup_interactive_session import (
    ApprovedPatch,
    FakeInteractiveSession,
    RepairOption,
)


patch = ApprovedPatch(
    kind="vocab_definition",
    target=Path("prompts/refund_python.prompt"),
    anchor={"finding_id": "R2-missing-vocabulary", "line": 42},
    replacement="- Remaining refundable amount: captured minus refunded.",
)
option = RepairOption(
    label="A",
    preview="--- prompt\n+++ prompt\n@@\n+definition",
    patch=patch,
)

session = FakeInteractiveSession(
    options_by_finding={"R2-missing-vocabulary": [option]},
    answers=["approve"],
)
session.seed({"findings": []})
presented = session.present_finding("R2-missing-vocabulary")
session.record_choice("R2-missing-vocabulary", presented[0])

assert session.ask("Apply option A?") == "approve"
assert session.approved_patches() == [patch]
