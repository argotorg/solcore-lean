#!/usr/bin/env python3
"""Code-image optimization protocol tests; no simulated EVM execution."""
import copy
import importlib.util
import subprocess
import sys
from pathlib import Path
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('image_exporter', ROOT/'scripts/export-rust-code-image.py')
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)


def envelope(level='O0'):
    return {'schema': exporter.SCHEMA, 'upstreamCommit': exporter.hull.COMMIT,
        'backend': {'name': 'sonatina', 'revision': exporter.BACKEND, 'optimization': level},
        'images': [{'path': ['Root'], 'bytes': '0x00', 'embeds': []}]}


class OptimizationProtocolTests(unittest.TestCase):
    def test_accepts_both_exact_requested_levels(self):
        for level in ('O0','O2'):
            exporter.validate_backend(envelope(level),level)

    def test_requested_level_cannot_be_relabelled(self):
        for expected,actual in [('O0','O2'),('O2','O0')]:
            with self.assertRaises(ValueError): exporter.validate_backend(envelope(actual),expected)
        for invalid in ('O1','O3','o2','',None):
            with self.assertRaises(ValueError): exporter.validate_backend(envelope(invalid),invalid)

    def test_rejects_changed_backend_revision_name_and_extra_metadata(self):
        for key,value in [('name','yul'),('revision','wrong'),('optimization','O1'),('extra',True)]:
            document=envelope('O2');document['backend'][key]=value
            with self.assertRaises(ValueError): exporter.validate_backend(document,'O2')
        for backend in (None,[],{},'sonatina'):
            document=envelope();document['backend']=backend
            with self.assertRaises(ValueError): exporter.validate_backend(document,'O0')

    def test_rejects_changed_envelope_and_missing_images(self):
        original=envelope()
        for key in original:
            document=copy.deepcopy(original);del document[key]
            with self.assertRaises(ValueError): exporter.validate_backend(document,'O0')
        for key,value in [('schema','wrong'),('upstreamCommit','wrong'),('images',None),('images',[]),('images',{}),('extra',True)]:
            document=copy.deepcopy(original);document[key]=value
            with self.assertRaises(ValueError): exporter.validate_backend(document,'O0')
        for document in (None,[],True):
            with self.assertRaises(ValueError): exporter.validate_backend(document,'O0')

    def test_cli_rejects_unknown_level_before_any_exporter_preparation(self):
        for invalid in ('O1','O3','o2'):
            process=subprocess.run([sys.executable,str(ROOT/'scripts/export-rust-code-image.py'),
                '--optimization',invalid,'--build','--upstream','/nonexistent/do-not-touch'],
                capture_output=True,text=True,timeout=10)
            self.assertEqual(process.returncode,2)
            self.assertIn('invalid choice',process.stderr)
            self.assertNotIn('exporter may only patch',process.stderr)

    def test_cli_documents_legacy_default_and_two_options(self):
        process=subprocess.run([sys.executable,str(ROOT/'scripts/export-rust-code-image.py'),'--help'],
            capture_output=True,text=True,timeout=10,check=True)
        self.assertIn('--optimization {O0,O2}',process.stdout)
        self.assertIn('default: O0',' '.join(process.stdout.split()))


if __name__=='__main__':
    unittest.main()
