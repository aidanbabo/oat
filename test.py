# todo: use pyright

import argparse
import dataclasses
from dataclasses import dataclass
from enum import Enum
import pathlib
import subprocess
import sys
from typing import List, Tuple

OAT = 'target/release/oat'

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

@dataclass
class Test:
    path: str
    exitcode: int = 0
    category: str = 'none'
    skip: str = ''
    interp_skip: str = ''
    todo: bool = False
    prints: str = b''
    passed_by_name: bool = False
    args: List[str] = dataclasses.field(default_factory=list)
    typecheck: str = ''

class TestResult(Enum):
    PASSED = 0
    FAILED = 1
    SKIPPED = 2

# todo: it isn't a str
def parse_test(filepath: str) -> Test:
    comment_str = '/*' if filepath.suffix == '.oat' else ';;'

    test_options = []
    with open(filepath) as testfile:
        for line in testfile:
            if not line.startswith(comment_str):
                break

            if filepath.suffix == '.oat':
                split = line[2:-3].strip().split(' ', 1)
            else:
                split = line[2:].strip().split(' ', 1)

            if len(split) == 2:
                opt, rest = split
                test_options.append((opt, rest))
            else:
                opt = split[0]
                test_options.append((opt, ''))

    test = test_from_options(filepath, test_options)
    return test

def test_from_options(filepath: str, options: List[Tuple[str, str]]) -> Test:
    is_oat = filepath.suffix == '.oat'
    test = Test(filepath)
    for opt, rest in options:
        if opt == 'exitcode':
            test.exitcode = int(rest)
        elif opt == 'category':
            test.category = rest
        elif opt == 'skip':
            test.skip = rest
        elif opt == 'interp_skip' and args.interpret_ll:
            test.skip = '(interpreter only) ' + rest
        elif opt == 'todo':
            test.todo = rest
        elif opt == 'prints':
            if rest.startswith('"'):
                # i hope nobody sees this!
                test.prints = eval(rest).encode('utf8')
            else:
                newline = '\n' if not is_oat else ''
                test.prints = (rest + newline).encode('utf8')
        elif opt == 'args':
            test.args = rest.split()
        elif opt == 'typecheck':
            assert rest in ['pass', 'fail']
            test.typecheck = rest
        elif args.debug:
            eprint(f"unrecognized test option for program at '{filepath}': '{opt}'")
    return test

def parse_tests(paths: List[str]) -> List[Test]:
    tests = []
    for p in paths:
        t = parse_test(p)
        tests.append(t)
    return tests

def eval_interp_test(test: Test, proc) -> TestResult:
    if proc.returncode != 0:
        eprint('FAILED INTERPRETER FAILED')
        return TestResult.FAILED

    lines = proc.stdout.rstrip().rsplit(b'\n', 1)
    if len(lines) == 2 and lines[1]:
        last_line = lines[1]
        prints = lines[0] + b'\n'
    else:
        last_line = lines[0]
        prints = b''

    line_split = last_line.rsplit(b' ', 1)
    if len(line_split) != 2:
        eprint('expected well formed last line')
        eprint(last_line)
        exit(1)
    [msg, exitcodestr] = line_split

    if msg == 'Interpreter Error:':
        eprint(f'Interpreter Error: {exitcodestr}')
        return TestResult.FAILED

    exitcode = int(exitcodestr)
    return eval_test(test, exitcode, prints)

def eval_test(test: Test, exitcode: int, prints: bytes) -> TestResult:
    if exitcode != test.exitcode:
        eprint(f"FAILED\nexpected an exit code of '{test.exitcode}' but it was '{exitcode}'")
        return TestResult.FAILED
    if prints != test.prints:
        eprint(f"FAILED\nexpected printed output '{test.prints}' but it printed '{prints}'")
        return TestResult.FAILED

    if test.todo:
        eprint(f'PASS (TODO {test.todo})')
    else:
        eprint('PASS')
    return TestResult.PASSED

def run_test(test: Test) -> TestResult:
    # todo: use tabs and longest test length
    eprint(f"\t{test.path}...", end='')
    if test.skip and not test.passed_by_name:
        eprint(f'SKIPPED ({test.skip})')
        return TestResult.SKIPPED

    proc_args = [OAT, test.path]
    if args.interpret_ll:
        proc_args.append('--interpret-ll')
    if args.clang:
        proc_args.append('--clang')
    if test.typecheck:
        proc_args.append('--check')
    # todo: program args to interpreter
    stderr = subprocess.PIPE if test.typecheck == 'fail' else None

    proc = subprocess.run(proc_args, stdout=subprocess.PIPE, stderr=stderr)

    if args.interpret_ll:
        return eval_interp_test(test, proc)
    else:
        if test.typecheck:

            if proc.returncode == 0 and test.typecheck == 'pass':
                eprint('PASS')
                return TestResult.PASSED
            elif proc.returncode == 101: # rust panic returncode
                eprint('FAILED\ncompiler panic')
                eprint(proc.stderr.decode('utf8') if proc.stderr else '')
                return TestResult.FAILED
            elif proc.returncode != 0 and test.typecheck == 'fail':
                eprint('PASS')
                return TestResult.PASSED
            elif proc.returncode == 0:
                eprint('FAILED\ncompilation should have failed, but succeeded')
                return TestResult.FAILED
            else:
                eprint('FAILED\ncompilation should have succeeded, but failed')
                return TestResult.FAILED

        if proc.returncode != 0:
            eprint('FAILED\ncompilation failed')
            return TestResult.FAILED

        proc = subprocess.run(['./a.out'] + test.args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return eval_test(test, proc.returncode, proc.stdout)

def filter_tests(tests: List[Test]) -> List[Test]:
    if args.category == 'all':
        tests = [t for t in tests if t.category != 'none']
    else:
        tests = [t for t in tests if t.category == args.category]
    return tests

def run_tests(tests: List[Test]):
    passed = failed = skipped = 0
    prev_category = None
    for i, t in enumerate(tests):
        if t.category != prev_category:
            prev_category = t.category
            print(f"Running {t.category} tests:")

        tr = run_test(t)
        if tr == TestResult.PASSED:
            passed += 1
        elif tr == TestResult.SKIPPED:
            skipped += 1
        elif tr == TestResult.FAILED:
            if args.early:
                print(f"exiting early. {len(tests) - i - 1} tests left unrun")
                break
            failed += 1
    print(f"{passed} passed, {failed} failed, {skipped} skipped")


def list_tests(tests: List[Test]):
    for t in tests:
        print(t.path)

def ll_files():
    files = [p for p in pathlib.Path('tests/programs/llprograms').glob('*.ll') if 'analysis' not in str(p)]
    return files

def hw4_files():
    files = [p for p in pathlib.Path('tests/programs/hw4programs').glob('*.oat')]
    return files

def hw5_files():
    files = [p for p in pathlib.Path('tests/programs/hw5programs').glob('*.oat')]
    return files

def custom_files():
    files = [p for p in pathlib.Path('tests/programs/custom').glob('*.oat')]
    return files

def main():

    cargo_build = subprocess.run(['cargo', 'build', '--release'])
    if cargo_build.returncode != 0:
        exit(1)

    if args.suite == 'all':
        files = hw4_files() + hw5_files() + custom_files() + ll_files()
        tests = parse_tests(files)
    elif args.suite == 'oat':
        files = hw4_files() + hw5_files() + custom_files()
        tests = parse_tests(files)
    elif args.suite == 'custom':
        files = custom_files()
        tests = parse_tests(files)
    elif args.suite == 'hw4':
        files = hw4_files()
        tests = parse_tests(files)
    elif args.suite == 'hw5':
        files = hw5_files()
        tests = parse_tests(files)
    elif args.suite == 'llvm':
        files = ll_files()
        tests = parse_tests(files)
    else:
        path = pathlib.Path(args.suite)
        t = parse_test(path)
        t.passed_by_name = True
        run_test(t)
        return

    tests = filter_tests(tests)
    tests.sort(key=lambda t: (t.category, t.path))
    # todo: group tests by category
    if args.list:
        list_tests(tests)
    else:
        run_tests(tests)

if __name__ == '__main__':
    llvm_test_categories = ['binop', 'calling-convention', 'memory', 'terminator', 'bitcast', 'gep', 'arith', 'large', 'io', 'uncategorized']
    hw4_test_categories = ['easiest', 'globals', 'path', 'easy', 'medium', 'hard', 'student', 'tc_hw4']
    hw5_test_categories = ['tc_eq', 'tc_subtyping', 'tc_statement', 'tc_expression', 'tc_struct', 'tc_global', 'tc_other', 'tc_ok', 'tc_err', 'struct', 'fptr', 'new']
    custom_categories = ['custom']

    parser = argparse.ArgumentParser()
    parser.add_argument('suite', default='all', nargs='?', choices=['all','oat', 'custom', 'hw4', 'hw5', 'llvm'])
    parser.add_argument('-c', '--category', choices=['all', 'none'] + llvm_test_categories + hw4_test_categories + hw5_test_categories + custom_categories, default='all')
    parser.add_argument('-l', '--list', action='store_true')
    parser.add_argument('--early', action='store_true')
    parser.add_argument('--interpret-ll', action='store_true', default=False)
    parser.add_argument('--clang', action='store_true', default=False)
    parser.add_argument('--debug', action='store_true', default=False)
    args = parser.parse_args()

    main()
