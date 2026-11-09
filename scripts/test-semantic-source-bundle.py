#!/usr/bin/env python3
"""Real filesystem/provenance integrity tests, without simulated compilation."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_bundle", ROOT / "scripts/semantic-source-bundle.py")
bundle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bundle)


def case_fixture():
    files = [{"path": name, "source": "// transport fixture: " + name + "\n"} for name in bundle.FILES]
    return {"source": files[0]["source"], "sourceBundle": {
        "schema": bundle.SCHEMA, "entry": "case.sol", "files": files}}


class BundleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.upstream = self.root / 'upstream'
        self.std = self.upstream / 'std'
        self.std.mkdir(parents=True)
        for name in ('std.sol', 'dispatch.sol'):
            (self.std / name).write_text('// pinned library fixture ' + name)
        self.tracked = ['std/dispatch.sol', 'std/std.sol']
        self.libraries = bundle.library_files(self.upstream, self.tracked)
        self.case = case_fixture()

    def tearDown(self):
        self.temp.cleanup()

    def write(self, name='run'):
        directory = self.root / name
        directory.mkdir()
        receipt = bundle.write(directory, self.case)
        receipt['libraries'] = self.libraries
        return directory, receipt

    def sources(self, receipt, names=bundle.FILES):
        return {**{uri: receipt['files'][name] for uri, name in receipt['generatedUris'].items() if name in names},
                **receipt['libraries']}

    def report(self, receipt, names=bundle.FILES):
        # Transport receipts only: no compiler success or execution is asserted.
        return {'sourceBundleReceipt': receipt, 'artifacts': receipt['files'].copy(),
                'exportProvenance': {'hull': {'sources': self.sources(receipt, names)}}}

    def test_exact_sorted_names_and_entry_alias_are_required(self):
        bundle.validate(self.case)
        changes = []
        for name in ('../left.sol', '/left.sol', 'x/left.sol', 'x\\left.sol', 'Left.sol', 'left.SOL', 'left.sol\x00'):
            value = copy.deepcopy(self.case)
            value['sourceBundle']['files'][2]['path'] = name
            changes.append(value)
        for action in ('missing', 'extra', 'duplicate', 'order', 'entry', 'alias', 'field'):
            value = copy.deepcopy(self.case)
            rows = value['sourceBundle']['files']
            if action == 'missing': rows.pop()
            elif action == 'extra': rows.append({'path': 'extra.sol', 'source': ''})
            elif action == 'duplicate': rows[3] = rows[2].copy()
            elif action == 'order': rows.reverse()
            elif action == 'entry': value['sourceBundle']['entry'] = 'left.sol'
            elif action == 'alias': value['source'] += '// changed'
            elif action == 'field': rows[0]['extra'] = True
            changes.append(value)
        for changed in changes:
            with self.assertRaises(ValueError):
                bundle.validate(changed)

    def test_write_is_exact_and_never_overwrites_an_existing_source(self):
        directory, receipt = self.write()
        for name, source in bundle.validate(self.case).items():
            self.assertEqual((directory / name).read_bytes(), source.encode())
        bundle.audit_files(directory, receipt['files'])
        with self.assertRaises(ValueError):
            bundle.write(directory, self.case)

    def test_provider_changes_missing_sources_extra_files_and_directories_fail(self):
        for change in ('content', 'missing', 'extra', 'directory', 'symlink'):
            directory, receipt = self.write(change)
            provider = directory / 'left.sol'
            if change == 'content': provider.write_text('// different provider')
            elif change == 'missing': provider.unlink()
            elif change == 'extra': (directory / 'unlisted.sol').write_text('// extra import')
            elif change == 'directory': (directory / 'modules').mkdir()
            else:
                provider.unlink()
                provider.symlink_to(self.std / 'std.sol')
            with self.assertRaises(ValueError):
                bundle.audit_files(directory, receipt['files'])

    def test_archive_inventory_must_include_even_a_provider_absent_from_hull_spans(self):
        directory, receipt = self.write()
        report = self.report(receipt, ('case.sol',))
        bundle.verify_archive(directory, self.case, report)
        del report['artifacts']['common.sol']
        with self.assertRaisesRegex(ValueError, 'omits'):
            bundle.verify_archive(directory, self.case, report)

    def test_archive_relocation_does_not_require_old_generated_files(self):
        directory, receipt = self.write('original')
        report = self.report(receipt, ('case.sol', 'left.sol'))
        old = bundle.normalized_sources(report['exportProvenance']['hull']['sources'], receipt, self.case)
        moved = self.root / 'moved archive'
        shutil.move(str(directory), moved)
        self.assertFalse(directory.exists())
        bundle.verify_archive(moved, self.case, report)
        fresh, new_receipt = self.write('fresh run')
        new = bundle.normalized_sources(self.sources(new_receipt, ('case.sol', 'left.sol')), new_receipt, self.case)
        self.assertEqual(old, new)
        self.assertEqual(set(new['files']), set(bundle.FILES))
        self.assertEqual(set(new['observedGenerated']), {'case.sol', 'left.sol'})
        self.assertNotEqual(receipt['generatedUris'], new_receipt['generatedUris'])
        self.assertTrue(fresh.is_dir())

    def test_foreign_same_basename_and_uri_aliases_cannot_be_normalized_as_generated(self):
        _, receipt = self.write()
        sources = self.sources(receipt)
        uri = next(uri for uri, name in receipt['generatedUris'].items() if name == 'left.sol')
        for foreign in ((self.root / 'foreign/left.sol').as_uri(), uri.replace('left.sol', 'left%2Esol'),
                uri + '?copy=1', uri + '#span', uri.replace('file:///', 'file://localhost/'),
                uri.replace('/left.sol', '/extra/../left.sol')):
            changed = {**sources, foreign: receipt['files']['left.sol']}
            with self.assertRaises(ValueError):
                bundle.normalized_sources(changed, receipt, self.case)

    def test_source_hash_changes_and_missing_entry_provenance_are_rejected(self):
        _, receipt = self.write()
        original = self.sources(receipt)
        for uri in original:
            changed = {**original, uri: '0' * 64}
            with self.assertRaises(ValueError):
                bundle.normalized_sources(changed, receipt, self.case)
        entry = next(uri for uri, name in receipt['generatedUris'].items() if name == 'case.sol')
        del original[entry]
        with self.assertRaisesRegex(ValueError, 'entry provenance'):
            bundle.normalized_sources(original, receipt, self.case)

    def test_generated_receipt_cannot_alias_names_or_mix_directories(self):
        _, receipt = self.write()
        left = next(uri for uri, name in receipt['generatedUris'].items() if name == 'left.sol')
        for mode in ('duplicate', 'foreign-parent', 'missing', 'wrong-hash', 'library-overlap'):
            changed = copy.deepcopy(receipt)
            if mode == 'duplicate': changed['generatedUris'][left] = 'right.sol'
            elif mode == 'foreign-parent':
                del changed['generatedUris'][left]
                changed['generatedUris'][(self.root / 'elsewhere/left.sol').as_uri()] = 'left.sol'
            elif mode == 'missing': del changed['generatedUris'][left]
            elif mode == 'wrong-hash': changed['files']['left.sol'] = '0' * 64
            else: changed['libraries'][left] = changed['files']['left.sol']
            with self.assertRaises(ValueError):
                bundle.validate_receipt(changed, self.case)

    def test_library_inventory_rejects_untracked_sources_symlinks_and_traversal(self):
        for names in ([], [*self.tracked, self.tracked[0]], ['std/../std/std.sol'], ['../std/std.sol']):
            with self.assertRaises(ValueError):
                bundle.library_files(self.upstream, names)
        extra = self.std / 'untracked.sol'
        extra.write_text('// unlisted')
        with self.assertRaises(ValueError):
            bundle.library_files(self.upstream, self.tracked)
        extra.unlink()
        provider = self.std / 'std.sol'
        provider.unlink()
        provider.symlink_to(self.std / 'dispatch.sol')
        with self.assertRaises(ValueError):
            bundle.library_files(self.upstream, self.tracked)

    def test_library_content_changes_are_observable_even_without_hull_spans(self):
        _, receipt = self.write('old')
        old = bundle.normalized_sources(self.sources(receipt, ('case.sol',)), receipt, self.case)
        (self.std / 'std.sol').write_text('// changed library')
        fresh = copy.deepcopy(receipt)
        fresh['libraries'] = bundle.library_files(self.upstream, self.tracked)
        entry_only = {uri: receipt['files'][name] for uri, name in receipt['generatedUris'].items() if name == 'case.sol'}
        new = bundle.normalized_sources(entry_only, fresh, self.case)
        self.assertNotEqual(old['libraries'], new['libraries'])
        with self.assertRaises(ValueError):
            bundle.normalized_sources(self.sources(fresh), receipt, self.case)


if __name__ == '__main__':
    unittest.main()
