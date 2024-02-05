import argparse
from dataclasses import dataclass
from enum import Enum
import pathlib
import subprocess
import sys
from typing import List

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

class TestResult(Enum):
    PASSED = 0
    FAILED = 1
    SKIPPED = 2

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
            else:
                if args.debug:
                    eprint('strange split length')
                continue
            test_options.append((opt, rest))

    test = Test(filepath)
    for opt, rest in test_options:
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
            test.prints = (rest + '\n').encode('utf8')
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
    eprint(f"running test at {test.path}...", end='')
    if test.skip and not test.passed_by_name:
        eprint(f'SKIPPED ({test.skip})')
        return TestResult.SKIPPED

    proc_args = [OAT, test.path]
    if args.interpret_ll:
        proc_args.append('--interpret-ll')
    if args.clang:
        proc_args.append('--clang')
    proc = subprocess.run(proc_args, stdout=subprocess.PIPE)

    if args.interpret_ll:
        return eval_interp_test(test, proc)
    else:
        if proc.returncode != 0:
            eprint('FAILED\ncompilation failed')
            return TestResult.FAILED
        proc = subprocess.run('./a.out', stdout=subprocess.PIPE)
        return eval_test(test, proc.returncode, proc.stdout)

def filter_tests(tests: List[Test]) -> List[Test]:
    if args.category == 'all':
        tests = [t for t in tests if t.category != 'none']
    else:
        tests = [t for t in tests if t.category == args.category]
    return tests

def run_tests(tests: List[Test]):
    passed = failed = skipped = 0
    for t in tests:
        tr = run_test(t)
        if tr == TestResult.PASSED:
            passed += 1
        elif tr == TestResult.SKIPPED:
            skipped += 1
        elif tr == TestResult.FAILED:
            if args.early:
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

def custom_files():
    files = [p for p in pathlib.Path('tests/programs/custom').glob('*.oat')]
    return files

def main():

    if not (args.interpret_ll or args.clang):
        eprint('must run through test through interpreter or use clang backend')
        exit(1)

    cargo_build = subprocess.run(['cargo', 'build', '--release'])
    if cargo_build.returncode != 0:
        exit(1)

    if args.suite == 'all':
        files = hw4_files() + custom_files()
        tests = parse_tests(files)
    elif args.suite == 'hw4':
        files = hw4_files()
        tests = parse_tests(files)
    elif args.suite == 'llvm':
        files = ll_files()
        tests = parse_tests(files)
    else:
        t = parse_test(args.suite)
        t.passed_by_name = True
        run_test(t)
        return

    tests = filter_tests(tests)
    tests.sort(key=lambda t: t.path)
    # todo: group tests by category
    if args.list:
        list_tests(tests)
    else:
        run_tests(tests)

if __name__ == '__main__':
    llvm_test_categories = ['binop', 'calling-convention', 'memory', 'terminator', 'bitcast', 'gep', 'arith', 'large', 'io', 'uncategorized']
    hw4_test_categories = ['easiest', 'globals', 'path']

    parser = argparse.ArgumentParser()
    parser.add_argument('suite', default='all', choices=['all', 'llvm', 'hw4'],  nargs='?')
    parser.add_argument('-c', '--category', choices=['all', 'none'] + llvm_test_categories + hw4_test_categories, default='all')
    parser.add_argument('-l', '--list', action='store_true')
    parser.add_argument('--early', action='store_true')
    parser.add_argument('--interpret-ll', action='store_true', default=False)
    parser.add_argument('--clang', action='store_true', default=False)
    parser.add_argument('--debug', action='store_true', default=False)
    args = parser.parse_args()

    main()
