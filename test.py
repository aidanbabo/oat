import argparse
from dataclasses import dataclass
import pathlib
import subprocess
import sys
from typing import List

OAT = 'target/debug/oat'

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

@dataclass
class Test:
    path: str
    exitcode: int = 0
    category: str = 'none'
    skip: str = ''
    todo: bool = False
    prints: str = b''
    passed_by_name: bool = False

def parse_test(filepath: str) -> Test:
    test_options = []
    with open(filepath) as testfile:
        for line in testfile:
            if not line.startswith(';;'):
                break
            opt, rest = line[2:].strip().split(' ', 1)
            test_options.append((opt, rest))

    test = Test(filepath)
    for opt, rest in test_options:
        if opt == 'exitcode':
            test.exitcode = int(rest)
        elif opt == 'category':
            test.category = rest
        elif opt == 'skip':
            test.skip = rest
        elif opt == 'todo':
            test.todo = rest
        elif opt == 'prints':
            test.prints = (rest + '\n').encode('utf8')
        else:
            eprint(f"unrecognized test option for program at '{filepath}': '{opt}'")
    return test

def parse_tests(paths: List[str]) -> List[Test]:
    tests = []
    for p in paths:
        t = parse_test(p)
        tests.append(t)
    return tests

def run_test(test: Test):
    # todo: use tabs and longest test length
    eprint(f"running test at {test.path}...", end='')
    if test.skip and not test.passed_by_name:
        eprint(f'SKIPPED ({test.skip})')
        return True

    proc = subprocess.run([OAT, test.path, '--interp-ll'], stdout=subprocess.PIPE)

    if proc.returncode != test.exitcode:
        eprint(f"FAILED\nexpected an exit code of '{test.exitcode}' but it was '{proc.returncode}'")
        return False
    if proc.stdout != test.prints:
        eprint(f"FAILED\nexpected printed output '{test.prints}' but it printed '{proc.stdout}'")
        return False

    if test.todo:
        eprint(f'PASS (TODO {test.todo})')
    else:
        eprint('PASS')
    return True

def filter_tests(tests: List[Test]) -> List[Test]:
    if args.category == 'all':
        pass
    elif args.category == 'not-none':
        tests = [t for t in tests if t.category != 'none']
    else:
        tests = [t for t in tests if t.category == args.category]
    return tests

def run_tests(tests: List[Test]):
    for t in tests:
        if not run_test(t):
            break

def list_tests(tests: List[Test]):
    for t in tests:
        print(t.path)

def main():
    cargo_build = subprocess.run(['cargo', 'build'])
    if cargo_build.returncode != 0:
        exit(1)

    if args.suite == 'all':
        eprint('the only supported testing right now is llvm')
        return
    elif args.suite == 'llvm':
        ll_files = [p for p in pathlib.Path('tests/programs/llprograms').glob('*.ll') if 'analysis' not in str(p)]
        tests = parse_tests(ll_files)
    else:
        t = parse_test(args.suite)
        t.passed_by_name = True
        run_test(t)
        return

    tests = filter_tests(tests)
    # todo: group tests by category and sort
    if args.list:
        list_tests(tests)
    else:
        run_tests(tests)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('suite', default='all', help="expected a suite name like 'all', 'llvm', or a filename", nargs='?')
    parser.add_argument('-c', '--category', choices=['all', 'none', 'not-none', 'binop', 'calling-convention', 'memory', 'terminator', 'bitcast', 'gep', 'arith', 'large', 'io'], default='all')
    parser.add_argument('-l', '--list', action='store_true')
    args = parser.parse_args()

    main()
