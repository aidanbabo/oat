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
        else:
            eprint(f"unrecognized test option for program at '{filepath}': '{opt}'")
    return test

def parse_tests(paths: List[str]) -> List[Test]:
    tests = []
    for p in paths:
        t = parse_test(p)
        tests.append(t)
    return tests

def run_test(test):
    eprint(f"running test at '{test.path}'... ", end='')
    proc = subprocess.run([OAT, test.path, '--interp-ll'])
    if proc.returncode != test.exitcode:
        eprint(f"FAILED\nexpected an exit code of '{test.exitcode}' but it was '{proc.returncode}'")
        return False
    eprint('PASS')
    return True

def run_tests(paths):
    tests = parse_tests(paths)
    if args.category != 'all':
        tests = [t for t in tests if t.category == args.category]

    for t in tests:
        if not run_test(t):
            break

def main():
    cargo_build = subprocess.run(['cargo', 'build'])
    if cargo_build.returncode != 0:
        exit(1)

    if args.suite == 'all':
        pass
    elif args.suite == 'llvm':
        ll_files = [p for p in pathlib.Path('tests/programs/llprograms').glob('*.ll') if 'analysis' not in str(p)]
        run_tests(ll_files)
    else:
        run_test(args.suite)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('suite', default='all', help="expected a suite name like 'all', 'llvm', or a filename", nargs='?')
    parser.add_argument('-c', '--category', choices=['binop', 'all', 'none'], default='all')
    args = parser.parse_args()

    main()
