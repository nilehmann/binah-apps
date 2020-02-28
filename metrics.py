import argparse
import glob
import os
import re
import shutil
import subprocess

APPS = {
    'conf': ['PaperIndex', 'PaperShow', 'ReviewShow'],
    'course': ['AssignmentShow', 'CourseIndex', 'SubmissionShow']
}
ROOT = os.path.abspath(os.path.dirname(__file__))


def run_lh(path, *extra_args):
    return subprocess.run(['stack', 'exec', '--', 'liquid', '-i', 'src'] + list(extra_args) + [path],
                          capture_output=True,
                          universal_newlines=True)


def remove_liquid():
    """Delete all .liquid directories recursively"""
    for liquid in glob.glob(os.path.join('**', '.liquid'), recursive=True):
        shutil.rmtree(liquid)


def metrics_for_controller(controller, n=1):
    print(f'{controller}', end='', flush=True)
    path = os.path.join('src', 'Controllers', f'{controller}.hs')
    s = 0
    for _ in range(n):
        completed = run_lh(path, '--time-binds')
        print('.', end='', flush=True)
        s += sum(map(float, re.findall(r"Time \(([^)s]+)s\)", completed.stdout)))
    print()
    return s / n


def metrics_for_app(app_name, clean=False):
    print(f'[Measuring {app_name}]')
    os.chdir(os.path.join(ROOT, app_name))
    if clean:
        print('Remove .liquid directories')
        remove_liquid()

        # Run on Model.hs first to get the error
        print('Running LH on src/Model.hs...')
        assert run_lh(os.path.join('src', 'Model.hs'), '--prune-unsorted').returncode != 0

        # We assume Main.hs imports all controllers
        print('Running LH on app/Main.hs...')
        run_lh(os.path.join('app', 'Main.hs'), '--prune-unsorted').returncode == 0

    results = {controller: metrics_for_controller(controller) for controller in APPS[app_name]}
    for controller, time in results.items():
        print(f'{controller}\t{time:0.2f}')


def main():
    parser = argparse.ArgumentParser(description='Process some integers.')
    parser.add_argument('--clean',
                        dest='clean',
                        action='store_true',
                        help='Remove all .liquid directories and start a clean check')
    parser.set_defaults(clean=False)

    args = parser.parse_args()

    for app_name in APPS:
        metrics_for_app(app_name, args.clean)


if __name__ == "__main__":
    main()
