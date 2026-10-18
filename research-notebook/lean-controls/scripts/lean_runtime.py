"""Resolve Lake without requiring this workspace's private tool installation."""
import os
from pathlib import Path
import shutil


def runtime(project: Path):
    env = dict(os.environ)
    bundled = project.parent / '.tools' / 'elan'
    if 'ELAN_HOME' not in env and (bundled / 'bin' / 'lake').is_file():
        env['ELAN_HOME'] = str(bundled)
    elan_lake = Path(env.get('ELAN_HOME', str(Path.home() / '.elan'))) / 'bin' / 'lake'
    lake = env.get('LAKE') or (str(elan_lake) if elan_lake.is_file() else shutil.which('lake'))
    if not lake:
        raise RuntimeError('Lake not found. Install elan or set LAKE to its executable path.')
    return str(lake), env
