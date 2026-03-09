"""
Entry point for the Euclid Simulator Python port.

Usage:
    python -m euclid_py                     # Launch GUI
    python -m euclid_py path/to/proof.json  # Launch and load proof
"""
from __future__ import annotations

import logging
import os
import sys
import traceback

from PyQt6.QtGui import QIcon
from PyQt6.QtWidgets import QApplication

from .ui.main_window import MainWindow


def _setup_crash_logging():
    """Install a global exception hook that writes to euclid_crash.log.

    This catches any unhandled exception (including those from Qt signal
    handlers) and writes a full traceback to the log file so the user
    can include it in bug reports.
    """
    log_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    log_path = os.path.join(log_dir, "euclid_crash.log")

    logger = logging.getLogger("euclid.crash")
    if not logger.handlers:
        logger.setLevel(logging.DEBUG)
        try:
            fh = logging.FileHandler(log_path, encoding="utf-8")
            fh.setLevel(logging.DEBUG)
            fmt = logging.Formatter(
                "%(asctime)s [%(levelname)s] %(message)s",
                datefmt="%Y-%m-%d %H:%M:%S",
            )
            fh.setFormatter(fmt)
            logger.addHandler(fh)
        except Exception:
            pass  # can't write log — silently continue

    _original_hook = sys.excepthook

    def _global_exception_hook(exc_type, exc_value, exc_tb):
        tb_text = "".join(traceback.format_exception(exc_type, exc_value, exc_tb))
        logger.critical("Unhandled exception:\n%s", tb_text)
        # Also print to stderr as usual
        _original_hook(exc_type, exc_value, exc_tb)

    sys.excepthook = _global_exception_hook


def main():
    _setup_crash_logging()

    # On Windows, set AppUserModelID so the taskbar shows our icon
    # instead of the default Python icon.
    try:
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
            "EuclidSim.Euclid.App.1")
    except (AttributeError, OSError):
        pass  # Non-Windows or unavailable

    app = QApplication(sys.argv)
    app.setApplicationName("Euclid")
    app.setOrganizationName("EuclidSim")
    app.setStyle("Fusion")

    # Set application icon
    icon_path = os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "Euclid Logo.png")
    if os.path.exists(icon_path):
        app.setWindowIcon(QIcon(icon_path))

    window = MainWindow()
    window.show()

    # If a proof JSON path is passed on the command line, load it directly
    args = app.arguments()
    if len(args) > 1 and args[1].endswith(".json"):
        window.open_proof_json(args[1])

    # Mark event loop as running so the proof panel uses background
    # threads for verification instead of blocking the UI.
    app.setProperty("_euclid_event_loop_running", True)

    sys.exit(app.exec())


if __name__ == "__main__":
    main()
