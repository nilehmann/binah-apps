import argparse
import glob
import os
import re
import shutil
import subprocess

import tabulate

APPS = {
    'conf': ['PaperIndex', 'PaperShow', 'ReviewShow'],
    'course': ['AssignmentShow', 'CourseIndex', 'SubmissionShow']
}
ROOT = os.path.abspath(os.path.dirname(__file__))


def count(path):
    insideLH = False
    annots = 0
    loc = 0
    for line in open(path, 'r'):
        line = line.strip()
        if not line:
            continue
        loc += 1

        if line.startswith('{-@'):
            assert not insideLH
            insideLH = True

        annots += insideLH

        if line.endswith('@-}'):
            assert insideLH
            insideLH = False

    return (loc, annots)


def ver_time(path, n):
    s = 0
    for _ in range(n):
        completed = run_lh(path, '--time-binds')
        print('.', end='', flush=True)
        s += sum(map(float, re.findall(r"Time \(([^)s]+)s\)", completed.stdout)))
    print()
    return s / n if n > 0 else 0


def run_lh(path, *extra_args):
    return subprocess.run(['stack', 'exec', '--', 'liquid', '-i', 'src'] + list(extra_args) + [path],
                          capture_output=True,
                          universal_newlines=True)


def remove_liquid():
    """Delete all .liquid directories recursively"""
    for liquid in glob.glob(os.path.join('**', '.liquid'), recursive=True):
        shutil.rmtree(liquid)


def metrics_for_controller(controller, n):
    print(f'{controller}', end='', flush=True)
    path = os.path.join('src', 'Controllers', f'{controller}.hs')
    loc, annots = count(path)
    return (loc, annots, ver_time(path, n))


def tabulate_metrics(metrics):
    rows = []
    total_loc = 0
    total_annots = 0
    total_time = 0
    for controller, (loc, annots, time) in metrics.items():
        rows.append([controller, str(loc), str(annots), f'{time:0.2f}'])
        total_loc += loc
        total_annots += annots
        total_time += time
    rows.append(["Total", str(total_loc), str(total_annots), f'{total_time:0.2f}'])
    return rows


def metrics_for_app(app_name, clean=False, n=3):
    print(f'[Measuring {app_name}]')
    print()
    os.chdir(os.path.join(ROOT, app_name))
    if clean:
        print('Remove .liquid directories')
        remove_liquid()

        # Run on Model.hs first to get the error
        print('Running LH on src/Model.hs...')
        assert run_lh(os.path.join('src', 'Model.hs'), '--prune-unsorted').returncode != 0

        # Run on Main.hs to get specs for all files
        # We assume Main.hs imports all controllers
        print('Running LH on app/Main.hs...')
        run_lh(os.path.join('app', 'Main.hs'), '--prune-unsorted').returncode == 0

    metrics = {controller: metrics_for_controller(controller, n) for controller in APPS[app_name]}
    tab = tabulate_metrics(metrics)
    print()
    print(
        tabulate.tabulate(tab,
                          headers=['Controller', 'LOC', 'Annots.', 'Ver. Time (s)'],
                          tablefmt='latex_booktabs'))
    print()


def main():
    parser = argparse.ArgumentParser(description='Process some integers.')
    parser.add_argument('--clean',
                        dest='clean',
                        action='store_true',
                        help='Remove all .liquid directories and start a clean check')
    parser.add_argument('--num', dest='n', type=int, metavar='N')
    parser.set_defaults(clean=False)

    args = parser.parse_args()

    for app_name in APPS:
        metrics_for_app(app_name, args.clean, args.n)


if __name__ == "__main__":
    main()
