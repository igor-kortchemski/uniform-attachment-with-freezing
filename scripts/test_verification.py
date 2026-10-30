#!/usr/bin/env python3
"""Failure-injection tests: real command boundaries, fake external checkers.

These tests do not run Lean or certify any mathematical result. They check
that failures cannot become a successful verification-script exit status.
Run: python3 -m unittest discover -s scripts -p test_verification.py -v
"""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parent
FAKE = r'''
import json, os
from pathlib import Path
import sys
name=Path(sys.argv[0]).name
args=sys.argv[1:]
def stage(label):
    with open(os.environ['FAKE_TRACE'],'a') as f: f.write(label+'\n')
    if os.environ.get('FAIL_STAGE')==label:
        print('injected failure: '+label, file=sys.stderr)
        sys.exit(7)
if name=='git':
    built=Path(os.environ['FAKE_TRACE']).exists() and 'build' in Path(os.environ['FAKE_TRACE']).read_text().splitlines()
    if args[:2]==['status','--porcelain']:
        if os.environ.get('FAKE_DIRTY') or (built and os.environ.get('DIRTY_AFTER_BUILD')): print(' M changed')
    elif args[:1]==['rev-parse']: print(('b' if built and os.environ.get('MOVE_AFTER_BUILD') else 'a')*40)
elif name=='lake':
    if args==['env','printenv','LEAN_SYSROOT']: print(os.environ['FAKE_TC'])
    elif args in (['env','lean','--version'],['--version']): print('fixture tool version')
    elif args[:1]==['build']: stage('build'); print('Build completed successfully (1 jobs).')
    elif args[:2]==['env','lean']:
        if '-c' in args:
            stage('compile diagnostic'); Path(args[args.index('-c')+1]).write_text('fake C')
        elif args[-1].endswith('AxiomAudit.lean'): stage('axiom-audit'); print('allowed')
        elif args[-1].endswith('MainResultsAxioms.lean'):
            stage('main-results-axioms')
            for i in range(26):
                ax='sorryAx' if os.environ.get('FAIL_STAGE')=='axiom-log' and i==25 else 'propext,\n Classical.choice, Quot.sound'
                print("'Query.N%d' depends on axioms: [%s]"%(i,ax))
        else: sys.exit(99)
    elif args[:1]==['env']: os.execv(args[1],args[1:])
    elif args[:1]==['comparator']: stage('official '+Path(args[-1]).stem)
    else: sys.exit(99)
elif name=='leanexport':
    stage('export challenge' if args[0].startswith('Challenge') else 'export solution')
    print('NDJSON'); print('export stderr, not NDJSON',file=sys.stderr)
elif name=='leanc':
    stage('link diagnostic')
    dest=Path(args[args.index('-o')+1]); dest.write_text(Path(__file__).read_text()); dest.chmod(0o755)
elif name=='localdiag':
    stage(Path(args[0]).stem+' comparison')
    if not os.environ.get('OMIT_CONFIRMATION'):
        print('compare: statements and reachable constants match'); print('axioms: only permitted axioms')
else:
    stage('nanoda' if name=='nanoda_bin' else name)
    if os.environ.get('MUTATE_EXPORT') and name=='leanchecker': Path(args[-1]).write_text('mutated during checking')
'''


class VerificationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='verification tests ')
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.root = self.base / 'project with spaces'
        scripts = self.root / 'scripts'
        scripts.mkdir(parents=True)
        for name in ('verification.py', 'collect-evidence.sh', 'local-comparator-diagnostic.sh',
                     'local-kernel-replay.sh', 'run-linux-checks.sh', 'check-axiom-log.py'):
            shutil.copy2(SCRIPTS / name, scripts / name)
        (scripts / 'MainResultsAxioms.lean').write_text('module\n' + ''.join(f'#print axioms Query.N{i}\n' for i in range(26)))
        (scripts / 'check-sources.py').write_text("import os,sys\nsys.exit(7 if os.environ.get('FAIL_STAGE')=='source-scan' else 0)\n")
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        data = {'challenge_module': 'Challenge.Test', 'solution_module': 'Solution.Test',
                'theorem_names': ['Query.N0'], 'definition_names': [],
                'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound']}
        (self.root / 'comparator').mkdir()
        for name in ('heights', 'locallimits', 'samelaw', 'sir'):
            (self.root / f'comparator/{name}.json').write_text(json.dumps(data))
        (self.root / 'comparator.json').write_text(json.dumps(data))
        self.bin = self.base / 'toolchain with spaces/bin'
        self.bin.mkdir(parents=True)
        for name in ('lake', 'git', 'leanexport', 'leanc', 'leanchecker', 'nanoda_bin',
                     'leanchecker-paranoid', 'lean4lean', 'con-leche', 'con-ron'):
            path = self.bin / name
            path.write_text(f'#!{sys.executable}\n' + FAKE)
            path.chmod(0o755)
        self.trace = self.base / 'trace.log'
        self.env = dict(os.environ, PATH=str(self.bin)+os.pathsep+os.environ['PATH'],
                        FAKE_TC=str(self.bin.parent), FAKE_TRACE=str(self.trace))
        self.solution = self.base / 'solution.ndjson'
        self.solution.write_text('NDJSON\n')

    def call(self, mode, out, fail=None, **extra):
        args = {'compare': ['comparator/heights.json', str(out)],
                'replay': ['comparator/heights.json', str(self.solution), str(out)],
                'collect': [str(out)], 'linux': [str(out)]}[mode]
        env = dict(self.env, **extra)
        if fail: env['FAIL_STAGE'] = fail
        return subprocess.run([sys.executable, str(self.root/'scripts/verification.py'), mode, *args],
                              cwd=self.base, env=env, capture_output=True, text=True)

    def test_compare_stops_at_each_failed_boundary(self):
        for label in ('export challenge', 'export solution', 'compile diagnostic', 'link diagnostic', 'heights comparison', 'leanchecker'):
            with self.subTest(label=label):
                out = self.base / label
                result = self.call('compare', out, fail=label)
                self.assertEqual(result.returncode, 7, result.stderr)
                self.assertEqual(json.loads((out/'result.json').read_text())['status'], 'failed')
                self.assertEqual(self.trace.read_text().splitlines()[-1], label)

    def test_compare_success_separates_export_stderr(self):
        out = self.base / 'compare'
        result = self.call('compare', out)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((out/'challenge.ndjson').read_text(), 'NDJSON\n')
        self.assertIn('export stderr', (out/'challenge-export.log').read_text())

    def test_zero_exit_without_success_confirmation_is_failure(self):
        result = self.call('compare', self.base/'missing confirmation', OMIT_CONFIRMATION='1')
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn('leanchecker', self.trace.read_text().splitlines())

    def test_every_selected_kernel_failure_propagates(self):
        for label in ('leanchecker', 'nanoda', 'leanchecker-paranoid', 'lean4lean', 'con-leche', 'con-ron'):
            with self.subTest(label=label):
                out = self.base / label
                result = self.call('replay', out, fail=label)
                self.assertEqual(result.returncode, 7, result.stderr)
                self.assertEqual(self.trace.read_text().splitlines()[-1], label)
                self.assertEqual(json.loads((out/'result.json').read_text())['status'], 'failed')

    def test_missing_kernel_is_failure(self):
        (self.bin/'nanoda_bin').unlink()
        result = self.call('replay', self.base/'missing kernel')
        self.assertEqual(result.returncode, 127)

    def test_collector_stops_on_failed_required_checks(self):
        for label in ('build', 'source-scan', 'axiom-audit', 'main-results-axioms', 'axiom-log',
                      'heights comparison', 'sir comparison', 'nanoda'):
            with self.subTest(label=label):
                out = self.base / ('collect '+label)
                result = self.call('collect', out, fail=label)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(json.loads((out/'result.json').read_text())['status'], 'failed')

    def test_successful_collector_finishes_all_interfaces(self):
        out = self.base/'full success'
        result = self.call('collect', out)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads((out/'result.json').read_text())['status'], 'passed')
        self.assertIn('comparator comparison', self.trace.read_text().splitlines())
        for label in ('heights','locallimits','samelaw','sir'):
            self.assertEqual(json.loads((out/label/'kernels/result.json').read_text())['status'], 'passed')

    def test_dirty_checkout_is_rejected_before_build(self):
        result = self.call('collect', self.base/'dirty', FAKE_DIRTY='1')
        self.assertEqual(result.returncode, 2)
        self.assertFalse(self.trace.exists())

    def test_checkout_change_during_run_cannot_be_certified(self):
        for variable in ('DIRTY_AFTER_BUILD', 'MOVE_AFTER_BUILD'):
            with self.subTest(variable=variable):
                self.trace.unlink(missing_ok=True)
                out = self.base/variable
                result = self.call('collect', out, **{variable:'1'})
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(json.loads((out/'result.json').read_text())['status'], 'failed')

    def test_export_change_during_checking_is_failure(self):
        for mode in ('compare', 'replay'):
            with self.subTest(mode=mode):
                result = self.call(mode, self.base/('mutate '+mode), MUTATE_EXPORT='1')
                self.assertNotEqual(result.returncode, 0)

    def test_stale_output_is_preserved_and_rejected(self):
        out = self.base/'old evidence'
        out.mkdir(); (out/'result.json').write_text('old success')
        result = self.call('compare', out)
        self.assertEqual(result.returncode, 2)
        self.assertEqual((out/'result.json').read_text(), 'old success')

    def test_forbidden_axiom_config_is_rejected_before_commands(self):
        path = self.root/'comparator/heights.json'
        data = json.loads(path.read_text()); data['permitted_axioms'].append('sorryAx')
        path.write_text(json.dumps(data))
        result = self.call('compare', self.base/'bad config')
        self.assertEqual(result.returncode, 2)
        self.assertFalse(self.trace.exists())

    def test_linux_official_failure_stops_later_interfaces(self):
        spec = importlib.util.spec_from_file_location('verification_fixture', self.root/'scripts/verification.py')
        module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        before = Path.cwd()
        self.addCleanup(os.chdir, before)
        with patch.dict(os.environ, dict(self.env, FAIL_STAGE='official samelaw'), clear=True), \
             patch.object(sys, 'platform', 'linux'), \
             patch.object(sys, 'argv', ['verification.py','linux',str(self.base/'linux')]):
            code = module.main()
        self.assertEqual(code, 7)
        self.assertNotIn('official sir', self.trace.read_text())
        configs = self.base/'linux/configs'
        for name in ('heights', 'locallimits', 'samelaw'):
            self.assertIs(json.loads((configs/f'{name}.json').read_text())['enable_nanoda'], True)

    def test_actual_non_linux_host_is_rejected_without_commands(self):
        if sys.platform == 'linux': self.skipTest('host is Linux')
        result = self.call('linux', self.base/'non linux')
        self.assertEqual(result.returncode, 2)
        self.assertFalse(self.trace.exists())


class AxiomLogTests(unittest.TestCase):
    def check(self, text, expected=1):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'axioms.log'; path.write_text(text)
            return subprocess.run([sys.executable, str(SCRIPTS/'check-axiom-log.py'), str(path), str(expected)], capture_output=True)

    def test_wrapped_and_axiom_free_reports(self):
        self.assertEqual(self.check("'T.a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n").returncode, 0)
        self.assertEqual(self.check("'T.a' does not depend on any axioms\n").returncode, 0)

    def test_duplicate_missing_error_and_forbidden_reports(self):
        for text, expected in [("'T.a' depends on axioms: [sorryAx]\n",1),
                               ("'T.a' depends on axioms: [propext]\n"*2,2),
                               ("'T.a' depends on axioms: [propext",1),
                               ("error: elaboration failed\n",0)]:
            with self.subTest(text=text): self.assertNotEqual(self.check(text,expected).returncode, 0)

    def test_wrong_names_cannot_replace_expected_queries(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp)/'queries.lean'; source.write_text('#print axioms Expected.name\n')
            log = Path(tmp)/'axioms.log'; log.write_text("'Wrong.name' depends on axioms: [propext]\n")
            proc = subprocess.run([sys.executable, str(SCRIPTS/'check-axiom-log.py'), str(log), '1', '--declarations', str(source)], capture_output=True)
            self.assertNotEqual(proc.returncode, 0)


class SummaryTests(unittest.TestCase):
    # Reuse setup/helpers without inheriting the other test cases.
    setUp = VerificationTests.setUp
    call = VerificationTests.call
    def test_summary_cannot_promote_failed_or_missing_evidence(self):
        out = self.base/'summary source'
        result = self.call('collect', out)
        self.assertEqual(result.returncode, 0, result.stderr)
        cmd = [sys.executable, str(SCRIPTS/'summarize-evidence.py'), str(out)]
        self.assertEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
        records = [out/'heights/result.json', out/'heights/kernels/result.json']
        originals = [p.read_bytes() for p in records]
        for path in records:
            data = json.loads(path.read_text()); data.pop('config_sha256'); path.write_text(json.dumps(data))
        self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
        for path, original in zip(records, originals): path.write_bytes(original)
        export = out/'heights/solution.ndjson'
        original = export.read_bytes()
        export.write_text('replaced export')
        self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
        export.unlink()
        self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)
        export.write_bytes(original)
        (out/'sir/kernels/kernels.log').write_text('nanoda exit=7\n')
        proc = subprocess.run(cmd, capture_output=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertNotIn(b'| sir | match', proc.stdout)
        (out/'result.json').unlink()
        self.assertNotEqual(subprocess.run(cmd, capture_output=True).returncode, 0)


if __name__ == '__main__': unittest.main()
