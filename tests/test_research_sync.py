"""Preservation boundaries for the notebook import; no Lean or network calls."""

import importlib.util
import tempfile
import unittest
from pathlib import Path

SPEC = importlib.util.spec_from_file_location(
    "research_sync",
    Path(__file__).resolve().parents[1] / "tools/sync_research_notebook.py",
)
sync_module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(sync_module)


class ResearchSyncTest(unittest.TestCase):
    def test_copy_update_and_keep_removed_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source"
            dest = root / "dest"
            source.mkdir()
            (source / "research").mkdir()
            proof = source / "research/Proof.lean"
            proof.write_text("first proof")
            runner = source / "research/check.sh"
            runner.write_text("#!/bin/sh\nexit 0\n")
            runner.chmod(0o755)
            cache = source / "research/.lake"
            cache.mkdir()
            (cache / "cache").write_text("ignore")
            sync_module.sync(source, dest)
            sync_module.sync(source, dest, check=True)
            self.assertFalse((dest / "research/.lake").exists())
            self.assertTrue((dest / "research/check.sh").stat().st_mode & 0o111)
            proof.write_text("updated proof")
            with self.assertRaisesRegex(RuntimeError, "out of date"):
                sync_module.sync(source, dest, check=True)
            sync_module.sync(source, dest)
            self.assertEqual(
                (dest / "research/Proof.lean").read_text(), "updated proof"
            )
            proof.unlink()
            sync_module.sync(source, dest)
            self.assertTrue((dest / "research/Proof.lean").exists())
            sync_module.sync(source, dest, check=True)

    def test_independent_destination_change_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source"
            dest = root / "dest"
            source.mkdir()
            (source / "AGENTS.md").write_text("original")
            sync_module.sync(source, dest)
            (dest / "AGENTS.md").write_text("manual destination edit")
            (source / "AGENTS.md").write_text("source update")
            with self.assertRaisesRegex(RuntimeError, "changed independently"):
                sync_module.sync(source, dest)
            self.assertEqual(
                (dest / "AGENTS.md").read_text(), "manual destination edit"
            )

    def test_destination_symlink_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source"
            dest = root / "dest"
            other = root / "other"
            source.mkdir()
            (source / "research").mkdir()
            (source / "research/Proof.lean").write_text("data")
            dest.mkdir()
            other.mkdir()
            (dest / "research").symlink_to(other)
            with self.assertRaisesRegex(RuntimeError, "symlink"):
                sync_module.sync(source, dest)
            self.assertFalse((other / "Proof.lean").exists())


if __name__ == "__main__":
    unittest.main()
