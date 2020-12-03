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
# TRIVIAL = re.compile(r"TaggedT\s*<\s*{\s*\\_\s*->\s*False\s*}\s*,\s*{\\_\s*->\s*True\s*}\s*>")
TRIVIAL = re.compile(r"(TaggedT\s*<\s*{\s*\\_\s*->\s*False\s*}\s*,\s*{\\_\s*->\s*True\s*}\s*>)|(TaggedT\s*<\s*{\s*\\_\s*->\s*True\s*}\s*,\s*{\\_\s*->\s*False\s*}\s*>)")
CLI_ARG = re.compile(r"LIQUID")

def do_loc(path, max_columns):
    c = collections.Counter({})

    annot = ""
    annot_lines = 0
    in_lh = False
    in_comment = False
    trivials = []
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

        c['comments'] += in_comment
        c['loc'] += not in_comment

        if in_lh:
            annot += stripped
            annot_lines += 1

        if in_comment and COMMENT_END.fullmatch(stripped) is not None:
            in_comment = False

        if in_lh and LH_END.fullmatch(stripped) is not None:
            if TRIVIAL.search(annot):
                c['trivial'] += 1
                c['trivial_lines'] += annot_lines
                trivials.append(annot)
            if not CLI_ARG.search(annot):
                c['annots'] += 1
                c['annots_lines'] += annot_lines
            annot = ""
            annot_lines = 0
            in_lh = False

    return (c, trivials)

def print_stats(stats):
    headers = ['loc', 'annots', 'trivial', 'annots_lines', 'trivial_lines', 'comments', 'empty']
    tab = [headers]
    tab.append([])
    for k in headers:
        tab[-1].append(stats[k])
    print(tabulate.tabulate(tab))
    print()

def print_trivials(trivials):
    print("Annotations counted as trivial")
    print("------------------------------")
    for t in trivials:
        print(t)

def main():
    parser = argparse.ArgumentParser(description='Process some integers.')
    parser.add_argument('-p', '--pattern',
                        help='Glob pattern')
    parser.add_argument('-f', '--file',
                        help='File')
    parser.add_argument('-e', '--exclude',
                        action="append",
                        help='Regex pattern to exclude')
    parser.add_argument('--columns', type=int, help="Maximum number of columns")
    parser.set_defaults(exclude=["Setup\.hs", "test/", "Model.hs", "Binah/.*", "Auth.hs"])
    # parser.set_defaults(exclude=[])
    parser.set_defaults(pattern="**/*.hs")
    parser.set_defaults(columns=100)

    args = parser.parse_args()

    exclude = [re.compile(e) for e in args.exclude]
    stats = collections.Counter({})
    trivials = []
    for path in glob.glob(args.pattern, recursive=True):
        should_exclude = any(e.search(path) for e in exclude)
        if should_exclude:
            continue
        try:
            next_stats, next_trivials = do_loc(path, args.columns)
            stats += next_stats
            trivials.extend(next_trivials)
        except Exception as e:
            print(path)
            raise e
    if args.file:
        next_stats, next_trivials = do_loc(args.file, args.columns)
        stats += next_stats
    print_stats(stats)
    print_trivials(trivials)

if __name__ == "__main__":
    main()
