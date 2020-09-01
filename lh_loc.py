import collections
import argparse
import glob
import os
import re

import tabulate

LH_START = re.compile(r"{-@.*")
LH_END = re.compile(r".*@-}")
COMMENT_START = re.compile(r"{-.*")
COMMENT_END = re.compile(r".*-}\s*")
TRIVIAL = re.compile(r"TaggedT\s*<\s*{\s*\\_\s*->\s*False\s*},\s*{\\_\s*->\s*True\s*}\s*>")
CLI_ARG = re.compile(r"LIQUID")

def do_loc(path):
    c = collections.Counter({})

    annot = ""
    in_lh = False
    in_comment = False
    for line in open(path, 'r'):
        line = line.strip()
        
        # An empty line
        if not line:
            c['empty'] += 1
            continue

        # A single line comment
        if line.startswith('--'):
            c['comments'] += 1
            continue

        assert len(line) <= 100, line

        # An import
        if line.startswith("import"):
            c['imports'] += 1

        if COMMENT_START.fullmatch(line) is not None:
            assert not in_comment
            in_comment = True

        if LH_START.fullmatch(line) is not None:
            assert not in_lh
            in_lh = True

        c['annots'] += in_lh
        c['comments'] += in_comment
        c['loc'] += not in_comment

        if in_lh:
            annot += line

        if COMMENT_END.fullmatch(line) is not None:
            assert in_comment
            in_comment = False

        if LH_END.fullmatch(line) is not None:
            assert in_lh
            if TRIVIAL.search(annot):
                print(annot)
                c['trivial'] += 1
            if CLI_ARG.search(annot):
                # we assume the cli arguments are written in a single line
                c['annots'] -= 1
            annot = ""
            in_lh = False

    return c


def main():
    parser = argparse.ArgumentParser(description='Process some integers.')
    parser.add_argument('-p', '--pattern',
                        help='Glob pattern')
    parser.add_argument('-e', '--exclude',
                        action="append",
                        help='Regex pattern to exclude')
    parser.set_defaults(exclude=["Setup\.hs", "test/", "Model.hs", "Binah/.*"])
    parser.set_defaults(pattern="**/*.hs")

    args = parser.parse_args()

    exclude = [re.compile(e) for e in args.exclude]
    locs = collections.Counter({})
    for path in glob.glob(args.pattern, recursive=True):
        should_exclude = any(e.search(path) for e in exclude)
        if should_exclude:
            continue
        try:
            locs += do_loc(path)
        except Exception as e:
            print(path)
            raise e
    print(locs)

if __name__ == "__main__":
    main()
