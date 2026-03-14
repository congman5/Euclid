"""
Resolve resource file paths for both normal Python and PyInstaller-frozen builds.

When the app is frozen into a standalone .exe with PyInstaller, data files
are extracted to a temporary ``sys._MEIPASS`` directory.  This module
provides a single helper that transparently handles both cases.
"""
from __future__ import annotations

import os
import sys


def resource_path(relative: str) -> str:
    """Return the absolute path to a bundled resource file.

    Parameters
    ----------
    relative : str
        Path relative to the project root (e.g. ``"Euclid Logo.png"``).

    Returns
    -------
    str
        Absolute filesystem path — works whether the app is running from
        source or from a PyInstaller bundle.
    """
    # PyInstaller sets sys._MEIPASS to the temp extraction directory
    base = getattr(sys, "_MEIPASS", None)
    if base is None:
        # Running from source — project root is two levels up from this file
        #   euclid_py/resources.py  →  euclid_py/  →  Euclid/
        base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, relative)
