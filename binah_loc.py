import collections
import argparse
import glob
import os
import re

def is_policy_code(line):
    line = line.strip()
    for s in ['predicate', 'policy', 'update', 'insert', 'read', 'assert']:
        if line.startswith(s):
            return True
    return False

def do_loc(path):
    c = collections.Counter()
    in_policy_code = False
    initial_indent = 0
    for line in open(path, 'r'):
        stripped = line.lstrip()
        indent = len(line) - len(stripped)
        if not stripped or stripped.startswith('--'):
            continue
        assert len(line) <= 101, line

        c['total'] += 1

        ended_with_curly_brace = False
        if in_policy_code and indent <= initial_indent:
            ended_with_curly_brace = stripped.startswith("}")
            in_policy_code = False

        if is_policy_code(line):
            initial_indent = indent
            in_policy_code = True

        c['models'] += not in_policy_code and not ended_with_curly_brace
        c['policy'] += in_policy_code or ended_with_curly_brace

    return c


def main():
    parser = argparse.ArgumentParser(description='Process some integers.')
    parser.add_argument('file', nargs='?')
    parser.set_defaults(file="src/Model.binah")

    args = parser.parse_args()

    print(do_loc(args.file))


if __name__ == "__main__":
    main()
