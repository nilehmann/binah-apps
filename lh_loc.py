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

def do_loc(path, max_columns):
    c = collections.Counter({})

    annot = ""
    in_lh = False
    in_comment = False
    for line in open(path, 'r'):
        stripped = line.strip()
        
        # An empty line
        if not stripped:
            c['empty'] += 1
            continue

        # A single line comment
        if stripped.startswith('--'):
            c['comments'] += 1
            continue

        assert len(line) <= max_columns, line

        # An import
        if line.startswith("import"):
            c['imports'] += 1

        if COMMENT_START.fullmatch(stripped) is not None:
            assert not in_comment
            in_comment = True

        if LH_START.fullmatch(stripped) is not None:
            assert not in_lh
            in_lh = True

        c['annots'] += in_lh
        c['comments'] += in_comment
        c['loc'] += not in_comment

        if in_lh:
            annot += stripped

        if in_comment and COMMENT_END.fullmatch(stripped) is not None:
            in_comment = False

        if in_lh and LH_END.fullmatch(stripped) is not None:
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
    parser.add_argument('--columns', type=int, help="Maximum number of columns")
    # parser.set_defaults(exclude=["Setup\.hs", "test/", "Model.hs", "Binah/.*"])
    parser.set_defaults(exclude=[])
    parser.set_defaults(pattern="**/*.hs")
    parser.set_defaults(columns=100)

    args = parser.parse_args()

    exclude = [re.compile(e) for e in args.exclude]
    locs = collections.Counter({})
    for path in glob.glob(args.pattern, recursive=True):
        should_exclude = any(e.search(path) for e in exclude)
        if should_exclude:
            continue
        try:
            a = do_loc(path, args.columns)
            print(a, path)
            locs += do_loc(path, args.columns)
        except Exception as e:
            print(path)
            raise e
    print(locs)

if __name__ == "__main__":
    main()
