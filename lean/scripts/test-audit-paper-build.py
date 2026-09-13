"""Axiom-output parser tests; these do not execute Lean."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('audit', Path(__file__).with_name('audit-paper-build.py'))
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


class AuditParserTests(unittest.TestCase):
    def test_standard(self):
        checks = mod.read_checks(["'N.foo' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]"])
        mod.validate_names(['N.foo'], checks)
        self.assertEqual(set(checks[0]['axioms']), mod.STANDARD)

    def test_no_axioms(self):
        checks = mod.read_checks(["'N.foo' does not depend on any axioms"])
        mod.validate_names(['foo'], checks)
        self.assertEqual(checks[0]['axioms'], [])

    def test_unexpected_axiom(self):
        with self.assertRaises(ValueError):
            mod.read_checks(["'N.foo' depends on axioms: [sorryAx]"])

    def test_wrong_name(self):
        with self.assertRaises(ValueError):
            mod.validate_names(['N.foo'], [{'theorem': 'N.bar', 'axioms': []}])

    def test_missing_output(self):
        with self.assertRaises(ValueError): mod.validate_names(['N.foo'], [])

    def test_extra_output(self):
        with self.assertRaises(ValueError):
            mod.validate_names([], [{'theorem': 'N.foo', 'axioms': []}])

    def test_ambiguous_short_name(self):
        with self.assertRaises(ValueError):
            mod.validate_names(['foo'], [{'theorem': 'N.foo'}, {'theorem': 'M.foo'}])

    def test_duplicate_command_needs_duplicate_output(self):
        with self.assertRaises(ValueError):
            mod.validate_names(['N.foo', 'N.foo'], [{'theorem': 'N.foo', 'axioms': []}])


if __name__ == '__main__': unittest.main()
