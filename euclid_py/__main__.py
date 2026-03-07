"""
Entry point for the Euclid Simulator Python port.

Usage:
    python -m euclid_py                     # Launch GUI
    python -m euclid_py path/to/proof.json  # Launch and load proof
"""
from __future__ import annotations

import os
import sys

from PyQt6.QtGui import QIcon
from PyQt6.QtWidgets import QApplication

from .ui.main_window import MainWindow


def main():
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

    sys.exit(app.exec())


if __name__ == "__main__":
    main()
