#!/usr/bin/env python3
"""Fixture tests of timing/provenance boundaries, not model capability tests."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from trial_runner import run

class RunnerChecks(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.root=Path(self.tmp.name)
        source=self.root/'statement.txt'; source.write_text('Fixture: 1+1=2.\n')
        self.case={'id':'fixture','preparation_status':'ready','statement_reviewed':True,
                   'source_inputs':[{'path':'statement.txt','sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'local_fixture':True}]}
        self.path=self.root/'case.json';self.write_case()
    def tearDown(self): self.tmp.cleanup()
    def write_case(self): self.path.write_text(json.dumps(self.case))
    def test_worker_claim_never_becomes_proof(self):
        result,path=run(self.path,[sys.executable,'-c','print("proved; million-dollar prize won")'],self.root/'runs',2)
        self.assertEqual(result['execution_status'],'completed')
        self.assertEqual(result['mathematical_status'],'unverified')
        self.assertFalse(result['solved'])
        self.assertTrue((path/'result.json').exists())
    def test_timeout_is_retained(self):
        result,path=run(self.path,[sys.executable,'-c','import time;time.sleep(30)'],self.root/'runs',0.1)
        self.assertEqual(result['execution_status'],'timed_out')
        self.assertLess(result['elapsed_seconds'],3)
        self.assertFalse(result['solved'])
    def test_modified_statement_rejected(self):
        (self.root/'statement.txt').write_text('Changed target')
        with self.assertRaises(ValueError): run(self.path,[sys.executable,'-c','pass'],self.root/'runs',1)
    def test_unprepared_metadata_rejected(self):
        self.case['preparation_status']='needs_statement';self.write_case()
        with self.assertRaises(ValueError): run(self.path,[sys.executable,'-c','pass'],self.root/'runs',1)
    def test_adapter_failure_is_distinct(self):
        result,_=run(self.path,[sys.executable,'-c','raise SystemExit(7)'],self.root/'runs',2)
        self.assertEqual(result['execution_status'],'adapter_failed')
        self.assertEqual(result['adapter_exit_code'],7)

if __name__=='__main__': unittest.main()
