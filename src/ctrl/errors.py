"""Errors that say what happened, why, and the exact command that fixes it.

Exit codes and error codes are part of the agent contract (docs/cli.md).
"""

from __future__ import annotations

EXIT_OK = 0
EXIT_ERROR = 1  # bad environment, missing tool, IO
EXIT_USAGE = 2
EXIT_NEEDS_HUMAN = 3  # statement not approved, review pending: wait, don't retry
EXIT_FAILED_CHECK = 4  # build, forbidden token, axiom, binding, hash drift
EXIT_REMOTE = 5  # Spark unreachable, job not found

# Stable error codes (docs/cli.md).
CODES = (
    "TOOL_MISSING",
    "LEAN_BUILD_FAILED",
    "FORBIDDEN_TOKEN",
    "NONSTANDARD_AXIOM",
    "BINDING_MISMATCH",
    "CHALLENGE_DRIFT",
    "NOT_APPROVED",
    "NO_FC_STATEMENT",
    "NEEDS_ANSWER",
    "EXISTS",
    "SPARK_UNREACHABLE",
    "JOB_NOT_FOUND",
    "REMOTE_FAILED",
    "BAD_USAGE",
    "INTERNAL",
)


class CtrlError(Exception):
    def __init__(
        self,
        code: str,
        message: str,
        hint: str = "",
        fix: str = "",
        exit_code: int = EXIT_ERROR,
    ) -> None:
        super().__init__(message)
        assert code in CODES, code
        self.code = code
        self.message = message
        self.hint = hint
        self.fix = fix
        self.exit_code = exit_code

    def to_dict(self) -> dict:
        return {"code": self.code, "message": self.message, "hint": self.hint, "fix": self.fix}


def usage(message: str, hint: str = "", fix: str = "") -> CtrlError:
    return CtrlError("BAD_USAGE", message, hint, fix, exit_code=EXIT_USAGE)


def from_exception(exc: BaseException) -> CtrlError:
    """Map stray exceptions onto CtrlError so every failure renders the same way."""
    if isinstance(exc, CtrlError):
        return exc
    if isinstance(exc, (FileNotFoundError, PermissionError, IsADirectoryError, OSError)):
        return CtrlError("TOOL_MISSING", str(exc), hint="a file or tool ctrl needs is not there")
    return CtrlError(
        "INTERNAL",
        f"{type(exc).__name__}: {exc}",
        hint="this is a bug in ctrl; report it with the command you ran",
    )
