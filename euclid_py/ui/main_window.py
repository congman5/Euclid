"""
Main Window — Fitch-style proof verifier UI.

Three screens:
  1. Home — Proposition browser with search/filter
  2. Proof — Split workspace: canvas + proof panel
  3. Verifier — Full Fitch-style proof verification environment

The Verifier screen is the primary UI, featuring:
  • Left sidebar: proof metadata, declarations, premises, goal, status
  • Center: custom-painted Fitch proof view with scope bars
  • Right sidebar: diagnostics + rule reference (tabbed)
  • Bottom: goals panel
"""
from __future__ import annotations

import json
import os
from collections import Counter
from typing import Dict, List, Optional

from PyQt6.QtCore import Qt, QSize, QTimer, QThread, QObject, QPropertyAnimation, QEasingCurve, pyqtProperty
from PyQt6.QtGui import QAction, QFont, QIcon, QColor, QPixmap, QPainter, QBrush, QPen
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QLabel, QPushButton, QListWidget, QListWidgetItem, QDialog,
    QSplitter, QToolBar, QStatusBar, QScrollArea, QFrame,
    QFileDialog, QMessageBox, QGroupBox, QStackedWidget, QTabWidget,
    QMenu,
)

from ..engine.proposition_data import (
    ALL_PROPOSITIONS, Proposition, get_proposition, get_allowed_propositions,
)
from ..engine.file_format import (
    save_proof, load_proof, save_journal_json, load_journal_json,
    detect_file_format,
)
from .canvas_widget import CanvasWidget, COLOR_PALETTE
from .proof_panel import ProofPanel
from .proof_view import ProofPanel as FitchProofPanel, ProofLineData
from .summary_panel import SummaryPanel
from .diagnostics_panel import DiagnosticsPanel
from .rule_reference import RuleReferencePanel
from .fitch_theme import C, Fonts, Sp, Sym, MAIN_STYLESHEET


# ═══════════════════════════════════════════════════════════════════════════
# COLOUR PALETTE
# ═══════════════════════════════════════════════════════════════════════════

COLORS = {
    "primary": "#2d70b3",
    "surface": "#ffffff",
    "background": "#f5f6f8",
    "text": "#1a1a2e",
    "textSecondary": "#6b7280",
    "border": "#e5e7eb",
    "accent": "#c9a84c",
    "error": "#d32f2f",
    "success": "#388e3c",
}


def _user_bookmarks_path() -> str:
    """Return the path to the user's saved bookmarks JSON file."""
    from ..resources import resource_path
    base = resource_path("")
    return os.path.join(base, "user_bookmarks.json")


def _load_user_bookmarks() -> list:
    """Load saved custom folders/files from disk."""
    path = _user_bookmarks_path()
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return []


def _save_user_bookmarks(bookmarks: list):
    """Persist custom folders/files to disk."""
    path = _user_bookmarks_path()
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(bookmarks, f, indent=2)
    except Exception:
        pass


_SB_BTN_STYLE = (
    "QPushButton {{ text-align: left; padding: 8px 10px;"
    " border: none; border-radius: 4px;"
    " background: transparent; color: {text};"
    " font-size: 12px; }}"
    " QPushButton:hover {{ background: #edf2ff; }}"
).format(text=COLORS['text'])

_SB_BTN_ACTIVE_STYLE = (
    "QPushButton {{ text-align: left; padding: 8px 10px;"
    " border: none; border-radius: 4px;"
    " background: #dce8f7; color: {text};"
    " font-size: 12px; }}"
    " QPushButton:hover {{ background: #dce8f7; }}"
).format(text=COLORS['text'])


class _OpenFileDialog(QDialog):
    """Custom file-open dialog with sidebar showing bundled proof folders
    and user-added custom folders/files."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Open Proof File")
        self.resize(720, 520)
        self.selected_path: str | None = None

        from ..resources import resource_path
        self._unsolved_dir = resource_path("unsolved_proofs")
        self._solved_dir = resource_path("solved_proofs")
        self._bookmarks = _load_user_bookmarks()

        root = QHBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        # ── Left sidebar ─────────────────────────────────────────────
        sidebar = QFrame()
        sidebar.setFixedWidth(200)
        sidebar.setStyleSheet(
            f"QFrame {{ background: {COLORS['surface']};"
            f" border-right: 1px solid {COLORS['border']}; }}")
        self._sb_layout = QVBoxLayout(sidebar)
        self._sb_layout.setContentsMargins(8, 12, 8, 12)
        self._sb_layout.setSpacing(2)

        sb_title = QLabel("Quick Access")
        sb_title.setFont(QFont("Segoe UI", 11, QFont.Weight.Bold))
        sb_title.setStyleSheet(
            f"color: {COLORS['text']}; border: none; padding: 0 0 6px 4px;")
        self._sb_layout.addWidget(sb_title)

        # Built-in folders
        self._sidebar_btns: list[tuple[QPushButton, str]] = []
        self._add_sidebar_entry(
            "\U0001f4d8  Unsolved Proofs", self._unsolved_dir, removable=False)
        self._add_sidebar_entry(
            "\u2705  Solved Proofs", self._solved_dir, removable=False)

        # User bookmarks
        for bm in self._bookmarks:
            path = bm.get("path", "")
            name = bm.get("name", os.path.basename(path))
            is_file = bm.get("type") == "file"
            icon = "\U0001f4c4" if is_file else "\U0001f4c1"
            self._add_sidebar_entry(
                f"{icon}  {name}", path, removable=True)

        # Spacer + add buttons
        self._sb_layout.addStretch()

        add_row = QHBoxLayout()
        add_row.setSpacing(4)

        btn_add_folder = QPushButton("+ Folder")
        btn_add_folder.setStyleSheet(
            "QPushButton { padding: 5px 8px; border: 1px solid #c0c8d4;"
            " border-radius: 4px; background: white;"
            f" color: {COLORS['text']}; font-size: 11px; }}"
            " QPushButton:hover { background: #f0f4ff; }")
        btn_add_folder.setToolTip("Add a folder to the sidebar")
        btn_add_folder.clicked.connect(self._add_folder_bookmark)
        add_row.addWidget(btn_add_folder)

        btn_add_file = QPushButton("+ File")
        btn_add_file.setStyleSheet(
            "QPushButton { padding: 5px 8px; border: 1px solid #c0c8d4;"
            " border-radius: 4px; background: white;"
            f" color: {COLORS['text']}; font-size: 11px; }}"
            " QPushButton:hover { background: #f0f4ff; }")
        btn_add_file.setToolTip("Add a single file to the sidebar")
        btn_add_file.clicked.connect(self._add_file_bookmark)
        add_row.addWidget(btn_add_file)

        self._sb_layout.addLayout(add_row)

        btn_browse = QPushButton("Browse\u2026")
        btn_browse.setStyleSheet(
            "QPushButton { padding: 7px 12px; border: 1px solid #c0c8d4;"
            " border-radius: 4px; background: white; margin-top: 4px;"
            f" color: {COLORS['text']}; font-size: 12px; }}"
            " QPushButton:hover { background: #f0f4ff; }")
        btn_browse.clicked.connect(self._browse_file)
        self._sb_layout.addWidget(btn_browse)

        root.addWidget(sidebar)

        # ── Right content — file list ────────────────────────────────
        right = QWidget()
        right.setStyleSheet("background: white;")
        rl = QVBoxLayout(right)
        rl.setContentsMargins(12, 12, 12, 12)
        rl.setSpacing(8)

        self._folder_label = QLabel("")
        self._folder_label.setFont(QFont("Segoe UI", 12, QFont.Weight.Bold))
        self._folder_label.setStyleSheet(f"color: {COLORS['text']};")
        rl.addWidget(self._folder_label)

        self._file_list = QListWidget()
        self._file_list.setStyleSheet(f"""
            QListWidget {{
                border: 1px solid {COLORS['border']};
                border-radius: 6px;
                background: white;
                outline: none;
                font-size: 13px;
            }}
            QListWidget::item {{
                padding: 10px 14px;
                border-bottom: 1px solid #f0f0f0;
            }}
            QListWidget::item:hover {{
                background: #f5f8ff;
            }}
            QListWidget::item:selected {{
                background: #dce8f7;
                color: {COLORS['primary']};
            }}
        """)
        self._file_list.itemDoubleClicked.connect(self._on_double_click)
        rl.addWidget(self._file_list)

        # Bottom buttons
        btn_row = QHBoxLayout()
        btn_row.addStretch()
        btn_cancel = QPushButton("Cancel")
        btn_cancel.setStyleSheet(
            "QPushButton { padding: 7px 20px; border: 1px solid #c0c8d4;"
            " border-radius: 4px; background: white;"
            f" color: {COLORS['text']}; font-size: 12px; }}"
            " QPushButton:hover { background: #f0f0f0; }")
        btn_cancel.clicked.connect(self.reject)
        btn_row.addWidget(btn_cancel)

        btn_open = QPushButton("Open")
        btn_open.setStyleSheet(
            f"QPushButton {{ padding: 7px 20px; border: none;"
            f" border-radius: 4px; background: {COLORS['primary']};"
            f" color: white; font-size: 12px; font-weight: 600; }}"
            f" QPushButton:hover {{ background: #1a5fa0; }}")
        btn_open.clicked.connect(self._on_open)
        btn_row.addWidget(btn_open)
        rl.addLayout(btn_row)

        root.addWidget(right, stretch=1)

        # Default to unsolved proofs
        self._active_path = None
        self._load_folder(self._unsolved_dir)

    # ── Sidebar helpers ───────────────────────────────────────────────

    def _add_sidebar_entry(self, label: str, path: str, removable: bool):
        """Add a button to the sidebar for a folder or file."""
        row = QHBoxLayout()
        row.setContentsMargins(0, 0, 0, 0)
        row.setSpacing(0)

        btn = QPushButton(label)
        btn.setStyleSheet(_SB_BTN_STYLE)
        btn.setCursor(Qt.CursorShape.PointingHandCursor)
        is_file = os.path.isfile(path)
        if is_file:
            btn.clicked.connect(
                lambda checked, p=path: self._select_file_directly(p))
        else:
            btn.clicked.connect(
                lambda checked, p=path: self._load_folder(p))
        row.addWidget(btn, stretch=1)

        if removable:
            rm_btn = QPushButton("\u00d7")
            rm_btn.setFixedSize(20, 20)
            rm_btn.setStyleSheet(
                "QPushButton { border: none; background: transparent;"
                " color: #aaa; font-size: 14px; }"
                " QPushButton:hover { color: #d32f2f; }")
            rm_btn.setCursor(Qt.CursorShape.PointingHandCursor)
            rm_btn.setToolTip("Remove from sidebar")
            rm_btn.clicked.connect(
                lambda checked, p=path: self._remove_bookmark(p))
            row.addWidget(rm_btn)

        container = QWidget()
        container.setLayout(row)
        # Insert before the stretch (which is after the last sidebar entry)
        insert_idx = len(self._sidebar_btns) + 1  # +1 for the title label
        self._sb_layout.insertWidget(insert_idx, container)
        self._sidebar_btns.append((btn, path))

    def _update_highlight(self, active_path: str):
        """Highlight the active sidebar button."""
        for btn, path in self._sidebar_btns:
            if path == active_path:
                btn.setStyleSheet(_SB_BTN_ACTIVE_STYLE)
            else:
                btn.setStyleSheet(_SB_BTN_STYLE)

    # ── Folder / file loading ─────────────────────────────────────────

    def _load_folder(self, folder: str):
        self._file_list.clear()
        self._active_path = folder
        basename = os.path.basename(folder)
        self._folder_label.setText(
            basename.replace("_", " ").title())
        self._update_highlight(folder)

        if not os.path.isdir(folder):
            item = QListWidgetItem("(folder not found)")
            item.setFlags(Qt.ItemFlag.NoItemFlags)
            self._file_list.addItem(item)
            return

        files = sorted(
            f for f in os.listdir(folder)
            if f.endswith(".euclid") and os.path.isfile(os.path.join(folder, f)))
        if not files:
            item = QListWidgetItem("(no .euclid files found)")
            item.setFlags(Qt.ItemFlag.NoItemFlags)
            self._file_list.addItem(item)
            return
        for fn in files:
            display = fn.replace(".euclid", "")
            item = QListWidgetItem(display)
            item.setData(Qt.ItemDataRole.UserRole, os.path.join(folder, fn))
            self._file_list.addItem(item)

    def _select_file_directly(self, path: str):
        """Sidebar file entry clicked — open it immediately."""
        if os.path.isfile(path):
            self.selected_path = path
            self.accept()

    def _on_double_click(self, item: QListWidgetItem):
        path = item.data(Qt.ItemDataRole.UserRole)
        if path:
            self.selected_path = path
            self.accept()

    def _on_open(self):
        item = self._file_list.currentItem()
        if item:
            path = item.data(Qt.ItemDataRole.UserRole)
            if path:
                self.selected_path = path
                self.accept()

    def _browse_file(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open Euclid File", "",
            "Euclid Files (*.euclid);;All Files (*)")
        if path:
            self.selected_path = path
            self.accept()

    # ── Bookmark management ───────────────────────────────────────────

    def _add_folder_bookmark(self):
        folder = QFileDialog.getExistingDirectory(
            self, "Add Folder to Sidebar")
        if not folder:
            return
        # Don't add duplicates
        for bm in self._bookmarks:
            if bm.get("path") == folder:
                self._load_folder(folder)
                return
        name = os.path.basename(folder)
        self._bookmarks.append({"path": folder, "name": name, "type": "folder"})
        _save_user_bookmarks(self._bookmarks)
        self._add_sidebar_entry(f"\U0001f4c1  {name}", folder, removable=True)
        self._load_folder(folder)

    def _add_file_bookmark(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Add File to Sidebar", "",
            "Euclid Files (*.euclid);;All Files (*)")
        if not path:
            return
        for bm in self._bookmarks:
            if bm.get("path") == path:
                return
        name = os.path.basename(path).replace(".euclid", "")
        self._bookmarks.append({"path": path, "name": name, "type": "file"})
        _save_user_bookmarks(self._bookmarks)
        self._add_sidebar_entry(f"\U0001f4c4  {name}", path, removable=True)

    def _remove_bookmark(self, path: str):
        self._bookmarks = [bm for bm in self._bookmarks if bm.get("path") != path]
        _save_user_bookmarks(self._bookmarks)
        # Remove from sidebar UI
        for i, (btn, bm_path) in enumerate(self._sidebar_btns):
            if bm_path == path:
                container = btn.parentWidget()
                if container:
                    self._sb_layout.removeWidget(container)
                    container.deleteLater()
                self._sidebar_btns.pop(i)
                break


class ToggleSwitch(QWidget):
    """iOS-style animated toggle switch."""

    def __init__(self, checked=True, parent=None):
        super().__init__(parent)
        self._checked = checked
        self._knob_x = 1.0 if checked else 0.0
        self.setFixedSize(40, 22)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

        self._anim = QPropertyAnimation(self, b"knob_position", self)
        self._anim.setDuration(150)
        self._anim.setEasingCurve(QEasingCurve.Type.InOutCubic)
        self._callback = None

    def set_toggled_callback(self, cb):
        self._callback = cb

    def isChecked(self):
        return self._checked

    def setChecked(self, val):
        if val != self._checked:
            self._checked = val
            self._animate(val)

    def _get_knob_position(self):
        return self._knob_x

    def _set_knob_position(self, val):
        self._knob_x = val
        self.update()

    knob_position = pyqtProperty(float, _get_knob_position, _set_knob_position)

    def _animate(self, on: bool):
        self._anim.stop()
        self._anim.setStartValue(self._knob_x)
        self._anim.setEndValue(1.0 if on else 0.0)
        self._anim.start()

    def mousePressEvent(self, event):
        self._checked = not self._checked
        self._animate(self._checked)
        if self._callback:
            self._callback(self._checked)
        event.accept()

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        r = h / 2
        off_color = QColor("#ccc")
        on_color = QColor(COLORS["primary"])
        t = self._knob_x
        track_color = QColor(
            int(off_color.red() + t * (on_color.red() - off_color.red())),
            int(off_color.green() + t * (on_color.green() - off_color.green())),
            int(off_color.blue() + t * (on_color.blue() - off_color.blue())),
        )
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(track_color))
        p.drawRoundedRect(0, 0, w, h, r, r)
        margin = 2
        knob_d = h - 2 * margin
        max_x = w - knob_d - margin
        knob_cx = margin + self._knob_x * (max_x - margin)
        p.setBrush(QBrush(QColor("white")))
        p.setPen(QPen(QColor(0, 0, 0, 30), 0.5))
        p.drawEllipse(int(knob_cx), margin, int(knob_d), int(knob_d))
        p.end()


class MainWindow(QMainWindow):
    """Root application window — switches between Workspace and Verifier screens."""

    # Target aspect ratio (width:height)
    _ASPECT_W = 14
    _ASPECT_H = 9

    def __init__(self):
        super().__init__()
        self.setWindowTitle("Euclid — Geometric Proof Verifier")
        self._apply_initial_geometry()
        self.setStyleSheet(MAIN_STYLESHEET)

        self._current_prop: Proposition | None = None

        # Stacked widget to swap screens
        self._stack = QStackedWidget()
        self.setCentralWidget(self._stack)

        # Build screens
        self._workspace = _WorkspaceScreen(self)
        self._verifier = _VerifierScreen(self)
        self._stack.addWidget(self._workspace)
        self._stack.addWidget(self._verifier)

        self._stack.setCurrentWidget(self._workspace)
        self.statusBar().showMessage("Ready — select a proposition or start a blank proof.")

    def _apply_initial_geometry(self):
        """Size the window to 85% of the available screen while keeping
        the target aspect ratio, then centre it on the primary display."""
        screen = QApplication.primaryScreen()
        if screen is None:
            self.resize(1400, 900)
            return
        avail = screen.availableGeometry()
        margin = 0.85
        max_w = int(avail.width() * margin)
        max_h = int(avail.height() * margin)

        # Fit the target ratio inside the available rectangle
        w = max_w
        h = int(w * self._ASPECT_H / self._ASPECT_W)
        if h > max_h:
            h = max_h
            w = int(h * self._ASPECT_W / self._ASPECT_H)

        self.resize(w, h)

        # Centre on screen
        x = avail.x() + (avail.width() - w) // 2
        y = avail.y() + (avail.height() - h) // 2
        self.move(x, y)

    # ── Navigation ────────────────────────────────────────────────────
    def _show_verifier(self):
        self._stack.setCurrentWidget(self._verifier)

    def open_proposition(self, prop: Proposition):
        self._current_prop = prop
        try:
            self._workspace.load_proposition(prop)
        except Exception as e:
            QMessageBox.critical(self, "Load Error",
                                 f"Failed to load proposition {prop.name}:\n{e}")
            return
        self._stack.setCurrentWidget(self._workspace)
        self.statusBar().showMessage(f"{prop.name} — {prop.title}")
        # Centre objects after the workspace is visible and laid out
        QTimer.singleShot(50, self._workspace._canvas.fit_to_contents)

    def open_proof_json(self, path: str):
        """Load a verifier-format JSON proof file and display in Fitch view."""
        self._verifier.load_proof_file(path)
        self._stack.setCurrentWidget(self._verifier)
        self.statusBar().showMessage(f"Loaded: {path}")

    def open_blank(self):
        blank = Proposition(
            id="blank", source="custom", book="Custom", name="New Proof",
            prop_number=None, max_proposition=48,
            title="Freeform Proof",
            statement="Write your own proposition here.",
        )
        self.open_proposition(blank)


# ═══════════════════════════════════════════════════════════════════════════
# VERIFIER SCREEN — Full Fitch-style proof verification environment
# ═══════════════════════════════════════════════════════════════════════════

class _VerifierScreen(QWidget):
    """
    Layout:
      ┌─────────────────────────────────────────────────────────┐
      │  Top bar: proof name, status, back, verify, load        │
      ├────────┬─────────────────────────────┬──────────────────┤
      │ Left   │  Center                     │  Right           │
      │ Summary│  Fitch proof view           │  Diagnostics     │
      │ Panel  │  (scrollable)               │  + Rule Ref      │
      │        │                             │  (tabbed)        │
      │        ├─────────────────────────────┤                  │
      │        │  Goals panel                │                  │
      └────────┴─────────────────────────────┴──────────────────┘
    """

    def __init__(self, main_win: MainWindow):
        super().__init__()
        self._mw = main_win
        self._proof_data: dict | None = None
        self._dirty = False
        self._verify_thread: QThread | None = None
        self._verify_worker: QObject | None = None

        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # ── Top bar ───────────────────────────────────────────────────
        topbar = QFrame()
        topbar.setFixedHeight(52)
        topbar.setStyleSheet(f"background:{C.header_bg}; border-bottom: none;")
        tl = QHBoxLayout(topbar)
        tl.setContentsMargins(16, 0, 16, 0)

        btn_back = QPushButton("← Home")
        btn_back.setStyleSheet(f"color:{C.header_text}; border: none; font-size: 13px; padding: 6px 12px;")
        btn_back.clicked.connect(self._back_with_save_check)
        tl.addWidget(btn_back)

        self._title_label = QLabel("Euclid Verifier")
        self._title_label.setFont(Fonts.ui_bold(14))
        self._title_label.setStyleSheet(f"color:{C.header_text};")
        tl.addWidget(self._title_label)

        self._status_label = QLabel()
        self._status_label.setFont(Fonts.ui_bold(12))
        self._status_label.setStyleSheet(f"color:{C.header_text}; padding: 4px 12px; border-radius: 4px;")
        tl.addWidget(self._status_label)

        tl.addStretch()

        btn_load = QPushButton("Load JSON")
        btn_load.setStyleSheet(f"color:{C.header_text}; border: 1px solid rgba(255,255,255,0.3); border-radius: 4px; padding: 6px 14px; font-size: 12px;")
        btn_load.clicked.connect(self._open_file)
        tl.addWidget(btn_load)

        btn_verify = QPushButton(f"{Sym.check} Verify")
        btn_verify.setStyleSheet(f"background: {C.valid}; color: white; border: none; border-radius: 4px; padding: 6px 16px; font-weight: bold; font-size: 13px;")
        btn_verify.clicked.connect(self._run_verification)
        tl.addWidget(btn_verify)
        self._verify_btn = btn_verify

        layout.addWidget(topbar)

        # ── Body: 3-column splitter ───────────────────────────────────
        body_splitter = QSplitter(Qt.Orientation.Horizontal)

        # Left: Summary panel
        self._summary = SummaryPanel()
        body_splitter.addWidget(self._summary)

        # Center: Proof panel (Fitch view + goals)
        self._proof_panel = FitchProofPanel()
        self._proof_panel.line_selected.connect(self._on_line_selected)
        body_splitter.addWidget(self._proof_panel)

        # Right: Tabbed diagnostics + rule reference
        right_tabs = QTabWidget()
        right_tabs.setStyleSheet(f"""
            QTabWidget::pane {{
                border: none;
                border-left: 1px solid {C.border};
                background: {C.surface};
            }}
            QTabBar {{
                background: {C.header_bg};
            }}
            QTabBar::tab {{
                padding: 8px 16px;
                font-size: 12px;
                color: rgba(255, 255, 255, 0.7);
                border: none;
                border-bottom: 2px solid transparent;
                background: transparent;
            }}
            QTabBar::tab:hover {{
                color: #ffffff;
                background: rgba(255, 255, 255, 0.08);
            }}
            QTabBar::tab:selected {{
                color: #ffffff;
                border-bottom: 2px solid {C.primary};
                background: rgba(255, 255, 255, 0.05);
            }}
        """)
        self._diagnostics = DiagnosticsPanel()
        self._diagnostics.navigate_to_line.connect(self._navigate_to_line)
        self._rule_ref = RuleReferencePanel()
        right_tabs.addTab(self._diagnostics, "Diagnostics")
        right_tabs.addTab(self._rule_ref, "Rules")
        body_splitter.addWidget(right_tabs)

        body_splitter.setStretchFactor(0, 1)   # summary — narrow
        body_splitter.setStretchFactor(1, 3)   # proof — dominant
        body_splitter.setStretchFactor(2, 1)   # right sidebar
        body_splitter.setSizes([240, 700, 320])
        layout.addWidget(body_splitter)

    # ── File loading ──────────────────────────────────────────────────

    def _cancel_verification(self):
        """Cancel any in-flight background verification."""
        if self._verify_thread is not None:
            if self._verify_worker is not None:
                self._verify_worker.cancel()
            try:
                self._verify_worker.line_checked.disconnect(self._on_line_checked)
            except (TypeError, RuntimeError, AttributeError):
                pass
            try:
                self._verify_worker.finished.disconnect(self._on_verify_finished)
            except (TypeError, RuntimeError, AttributeError):
                pass
            try:
                self._verify_worker.finished.disconnect(self._verify_thread.quit)
            except (TypeError, RuntimeError, AttributeError):
                pass
            self._verify_thread.quit()
            if not self._verify_thread.wait(3000):
                self._verify_thread.terminate()
                self._verify_thread.wait(1000)
            self._verify_thread.deleteLater()
            self._verify_thread = None
            self._verify_worker = None
        self._verify_btn.setEnabled(True)

    def _open_file(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open Proof JSON", "", "JSON Files (*.json);;All Files (*)"
        )
        if path:
            self.load_proof_file(path)

    def load_proof_file(self, path: str):
        # Cancel any in-flight verification before loading new data
        self._cancel_verification()
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            QMessageBox.critical(self, "Load Error", f"Failed to load proof:\n{e}")
            return

        # Convert .euclid format to flat verifier format if needed
        if "proof" in data and "steps" in data.get("proof", {}):
            from .proof_panel import ProofPanel
            data = ProofPanel._euclid_to_verifier(data)

        self._proof_data = data
        self._last_save_path = path
        self._dirty = True
        self._display_proof(data)
        self._run_verification()

    # ── Display proof without verification ────────────────────────────

    def _display_proof(self, data: dict):
        try:
            name = data.get("name", "untitled")
            self._title_label.setText(f"Euclid — {name}")

            decl = data.get("declarations", {})
            self._summary.set_proof_info(
                name=name,
                points=decl.get("points", []),
                lines_decl=decl.get("lines", []),
                premises=data.get("premises", []),
                goal=data.get("goal", ""),
            )

            # Build display lines (pending status before verification)
            lines_data = []
            for ld in data.get("lines", []):
                lines_data.append(ProofLineData(
                    line_id=ld["id"],
                    depth=ld.get("depth", 0),
                    formula_text=ld.get("statement", ""),
                    justification=ld.get("justification", ""),
                    refs=ld.get("refs", []),
                    is_assumption=(ld.get("justification", "") == "Assume"),
                    status="pending",
                    diagnostics=[],
                ))

            self._proof_panel.set_proof_data(
                lines_data,
                goal_text=data.get("goal", ""),
                goal_achieved=None,
            )
            self._diagnostics.set_diagnostics([])
        except Exception as e:
            QMessageBox.warning(self, "Display Error",
                                f"Error displaying proof data:\n{e}")

    # ── Run verification ──────────────────────────────────────────────

    def _run_verification(self):
        if self._proof_data is None:
            return
        # Ignore if a verification is already running
        if self._verify_thread is not None:
            return

        # When no event loop is running (e.g. tests), fall back to
        # synchronous verification to avoid hanging.
        app = QApplication.instance()
        if app is None or not app.property("_euclid_event_loop_running"):
            try:
                from verifier.unified_checker import verify_e_proof_json
                result = verify_e_proof_json(self._proof_data)
            except Exception as exc:
                return
            self._on_verify_finished(result)
            return

        # Disable Verify button and show busy status
        self._verify_btn.setEnabled(False)
        self._status_label.setText(" \u23f3 Verifying\u2026 ")
        self._status_label.setStyleSheet(
            f"color:{C.header_text}; padding: 4px 12px;"
            f" border-radius: 4px; font-weight: bold;")
        self._mw.statusBar().showMessage("Verifying\u2026")

        # Show all lines as pending (?) before verification starts
        pending_lines = []
        for ld in self._proof_data.get("lines", []):
            pending_lines.append(ProofLineData(
                line_id=ld["id"],
                depth=ld.get("depth", 0),
                formula_text=ld.get("statement", ""),
                justification=ld.get("justification", ""),
                refs=ld.get("refs", []),
                is_assumption=(ld.get("justification", "") == "Assume"),
                status="pending",
                diagnostics=[],
                is_goal_line=False,
            ))
        self._proof_panel.set_proof_data(
            pending_lines,
            goal_text=self._proof_data.get("goal", ""),
            goal_achieved=None,
        )

        # Import the worker from proof_panel (shared implementation)
        from .proof_panel import _VerifyWorker

        self._verify_thread = QThread()
        self._verify_worker = _VerifyWorker(self._proof_data)
        self._verify_worker.moveToThread(self._verify_thread)
        self._verify_thread.started.connect(self._verify_worker.run)
        self._verify_worker.line_checked.connect(
            self._on_line_checked, Qt.ConnectionType.QueuedConnection)
        self._verify_worker.finished.connect(self._on_verify_finished)
        self._verify_worker.finished.connect(self._verify_thread.quit)
        self._verify_thread.start()

    def _on_line_checked(self, line_id: int, valid: bool, errors: list):
        """Update a single line's status as verification progresses."""
        status = "valid" if valid else "invalid"
        self._proof_panel.update_line_status(line_id, status)

    def _on_verify_finished(self, result_or_exc):
        """Handle verification result from the background thread."""
        # Clean up thread references — wait for thread exit before
        # destroying to avoid 'QThread: Destroyed while still running'.
        if self._verify_thread is not None:
            self._verify_thread.quit()
            self._verify_thread.wait(2000)
            self._verify_thread.deleteLater()
        self._verify_thread = None
        self._verify_worker = None

        # Re-enable Verify button
        self._verify_btn.setEnabled(True)

        # Handle verifier exception
        if isinstance(result_or_exc, Exception):
            QMessageBox.warning(
                self, "Verification Error",
                f"Verifier raised an exception:\n{result_or_exc}")
            return

        result = result_or_exc

        # Determine which lines passed / failed
        error_line_ids = {lid for lid, lr in result.line_results.items()
                          if not lr.valid}

        # Build display lines with verification status
        lines_data = []
        rule_counts: Counter = Counter()
        for ld in self._proof_data.get("lines", []):
            lid = ld["id"]
            just = ld.get("justification", "")
            rule_counts[just] += 1

            if lid in error_line_ids:
                status = "invalid"
            elif lid in result.derived:
                status = "valid"
            else:
                status = "pending"

            lr = result.line_results.get(lid)
            diag_list = [{"line": lid, "message": e}
                         for e in (lr.errors if lr else [])]

            lines_data.append(ProofLineData(
                line_id=lid,
                depth=ld.get("depth", 0),
                formula_text=ld.get("statement", ""),
                justification=just,
                refs=ld.get("refs", []),
                is_assumption=(just == "Assume"),
                status=status,
                diagnostics=diag_list,
                is_goal_line=False,
            ))

        goal_achieved = result.accepted if self._proof_data.get("goal") else None
        self._proof_panel.set_proof_data(
            lines_data,
            goal_text=self._proof_data.get("goal", ""),
            goal_achieved=goal_achieved,
        )

        # Update diagnostics panel
        all_diags = []
        for lid, lr in result.line_results.items():
            for e in lr.errors:
                all_diags.append({"line": lid, "message": e, "code": "ERROR"})
        for e in result.errors:
            all_diags.append({"line": 0, "message": e, "code": "ERROR"})
        self._diagnostics.set_diagnostics(all_diags)

        num_errors = sum(1 for lr in result.line_results.values()
                          if not lr.valid) + len(result.errors)

        # Update summary panel
        self._summary.set_result(
            accepted=result.accepted,
            num_lines=len(lines_data),
            num_errors=num_errors,
            first_error_line=min(error_line_ids) if error_line_ids else None,
            goal_derived_on=None,
            rule_counts=dict(rule_counts),
        )

        # Update status in top bar
        if result.accepted:
            self._status_label.setText(f" {Sym.check} ACCEPTED ")
            self._status_label.setStyleSheet(f"background: {C.valid}; color: white; padding: 4px 12px; border-radius: 4px; font-weight: bold;")
        else:
            self._status_label.setText(f" {Sym.cross} REJECTED ")
            self._status_label.setStyleSheet(f"background: {C.invalid}; color: white; padding: 4px 12px; border-radius: 4px; font-weight: bold;")

        self._mw.statusBar().showMessage(
            f"Verification complete — {'ACCEPTED' if result.accepted else 'REJECTED'}"
            f" | {num_errors} diagnostic(s)"
        )

    # ── Save / back ───────────────────────────────────────────────────

    def _back_with_save_check(self):
        """Prompt to save unsaved changes before navigating home."""
        if self._dirty:
            reply = QMessageBox.question(
                self, "Unsaved Changes",
                "You have unsaved changes. Would you like to save before leaving?",
                QMessageBox.StandardButton.Save
                | QMessageBox.StandardButton.Discard
                | QMessageBox.StandardButton.Cancel,
            )
            if reply == QMessageBox.StandardButton.Save:
                self._save_proof()
                self._mw._stack.setCurrentWidget(self._mw._workspace)
            elif reply == QMessageBox.StandardButton.Discard:
                self._dirty = False
                self._mw._stack.setCurrentWidget(self._mw._workspace)
            # Cancel → stay on verifier
        else:
            self._mw._stack.setCurrentWidget(self._mw._workspace)

    def _save_proof(self):
        """Save the current proof data back to a JSON file."""
        default = getattr(self, '_last_save_path', '') or ''
        path, _ = QFileDialog.getSaveFileName(
            self, "Save Proof JSON", default,
            "JSON Files (*.json);;All Files (*)",
        )
        if path and self._proof_data is not None:
            try:
                with open(path, "w", encoding="utf-8") as f:
                    json.dump(self._proof_data, f, indent=2)
                self._dirty = False
                self._mw.statusBar().showMessage(f"Saved to {path}")
            except Exception as e:
                QMessageBox.critical(self, "Save Error", f"Failed to save:\n{e}")

    # ── Interactions ──────────────────────────────────────────────────

    def _on_line_selected(self, line_id: int):
        self._mw.statusBar().showMessage(f"Selected line {line_id}")

    def _navigate_to_line(self, line_id: int):
        self._proof_panel.scroll_to_line(line_id)
        self._proof_panel.proof_view.select_line(line_id)


# ═══════════════════════════════════════════════════════════════════════════
# WORKSPACE SCREEN (canvas + proof panel)
# ═══════════════════════════════════════════════════════════════════════════

class _WorkspaceScreen(QWidget):
    def __init__(self, main_win: MainWindow):
        super().__init__()
        self._mw = main_win
        self._current_prop: Proposition | None = None
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # ── Top toolbar ───────────────────────────────────────────────
        toolbar = QFrame()
        toolbar.setFixedHeight(48)
        toolbar.setStyleSheet(f"""
            QFrame {{
                background: {COLORS['surface']};
                border-bottom: 1px solid {COLORS['border']};
            }}
            QPushButton {{
                background: {COLORS['surface']};
                color: {COLORS['text']};
                border: 1px solid {COLORS['border']};
                border-radius: 4px;
                padding: 6px 14px;
                font-size: 13px;
            }}
            QPushButton:hover {{
                background: #f0f4ff;
                border-color: {COLORS['primary']};
            }}
        """)
        tl = QHBoxLayout(toolbar)
        tl.setContentsMargins(12, 0, 12, 0)

        btn_new = QPushButton("+ New Proof")
        btn_new.clicked.connect(self._new_blank_proof)
        tl.addWidget(btn_new)

        self._title_label = QLabel()
        self._title_label.setFont(QFont("Segoe UI", 13, QFont.Weight.Bold))
        self._title_label.setStyleSheet(f"color: {COLORS['text']};")
        tl.addWidget(self._title_label)
        tl.addStretch()

        btn_save = QPushButton("Save")
        btn_save.clicked.connect(self._save)
        tl.addWidget(btn_save)

        btn_open = QPushButton("Open")
        btn_open.clicked.connect(self._import)
        tl.addWidget(btn_open)

        self._btn_ref = QPushButton("Reference")
        self._btn_ref.setCheckable(True)
        self._btn_ref.setToolTip("Toggle System E rule reference panel")
        self._btn_ref.setStyleSheet(f"""
            QPushButton {{
                background: {COLORS['surface']};
                color: {COLORS['text']};
                border: 1px solid {COLORS['border']};
                border-radius: 4px;
                padding: 6px 14px;
                font-size: 13px;
            }}
            QPushButton:hover {{
                background: #f0f4ff;
                border-color: {COLORS['primary']};
            }}
            QPushButton:checked {{
                background: {COLORS['primary']};
                color: white;
                border-color: {COLORS['primary']};
            }}
        """)
        self._btn_ref.clicked.connect(self._toggle_reference)
        tl.addWidget(self._btn_ref)

        layout.addWidget(toolbar)

        # ── Main body: splitter with canvas-side vs proof panel ────────
        # The proof journal spans full height (below the top toolbar)
        # while the drawing bar + color bar sit above the canvas only.
        body_splitter = QSplitter(Qt.Orientation.Horizontal)

        # Left side: drawing bar + color bar + canvas (stacked)
        canvas_container = QWidget()
        canvas_vbox = QVBoxLayout(canvas_container)
        canvas_vbox.setContentsMargins(0, 0, 0, 0)
        canvas_vbox.setSpacing(0)

        # ── Drawing tool bar (horizontally scrollable) ──────────────────
        _tb_style = (
            f"QPushButton {{ background:{COLORS['surface']}; color:{COLORS['text']};"
            f" border:1px solid {COLORS['border']}; border-radius:3px;"
            " padding:3px 8px; font-size:14px; min-width:24px; }}"
            f" QPushButton:hover {{ background:#f0f4ff;"
            f" border-color:{COLORS['primary']}; }}"
            f" QPushButton:checked {{ background:{COLORS['primary']};"
            " color:white; }}"
            " QLabel { font-size:12px; }"
        )
        draw_inner = QWidget()
        draw_inner.setStyleSheet(_tb_style)
        draw_inner.setAutoFillBackground(True)
        pal = draw_inner.palette()
        pal.setColor(draw_inner.backgroundRole(), QColor(COLORS['background']))
        draw_inner.setPalette(pal)
        draw_row = QHBoxLayout(draw_inner)
        draw_row.setContentsMargins(4, 2, 4, 2)
        draw_row.setSpacing(3)

        self._tools: dict[str, QPushButton] = {}
        tool_defs = [
            ("select", "⇱", "Select / drag points"),
            ("pan", "✥", "Pan canvas"),
            None,
            ("label", "A", "Label / rename point"),
            ("point", "•", "Place point"),
            ("segment", "—", "Draw segment"),
            ("ray", "→", "Draw ray"),
            ("circle", "○", "Draw circle (center + radius point)"),
            ("angle", "∠", "Measure angle (click 3 existing points)"),
            ("perpendicular", "∟", "Mark right angle (click 3 existing points, must be 90°)"),
            None,
            ("construct", "🔨", "Proposition construction (guided construction rules)"),
            ("equal", "\u2245", "Assert segments equal (click two segments)"),
            ("delete", "✕", "Delete object"),
            None,
        ]
        for entry in tool_defs:
            if entry is None:
                sep = QFrame()
                sep.setFixedSize(1, 22)
                sep.setStyleSheet(f"background:{COLORS['border']};")
                draw_row.addWidget(sep)
                continue
            tid, label, tip = entry
            b = QPushButton(label)
            b.setToolTip(tip)
            b.setCheckable(True)
            b.setFixedHeight(26)
            b.clicked.connect(lambda checked, t=tid, btn=b: self._set_tool_btn(t))
            draw_row.addWidget(b)
            self._tools[tid] = b

        # Undo / Redo
        btn_undo = QPushButton("↩")
        btn_undo.setToolTip("Undo (Ctrl+Z)")
        btn_undo.setFixedHeight(26)
        btn_undo.clicked.connect(lambda: self._canvas.undo())
        draw_row.addWidget(btn_undo)
        btn_redo = QPushButton("↪")
        btn_redo.setToolTip("Redo (Ctrl+Y)")
        btn_redo.setFixedHeight(26)
        btn_redo.clicked.connect(lambda: self._canvas.redo())
        draw_row.addWidget(btn_redo)

        sep2 = QFrame()
        sep2.setFixedSize(1, 22)
        sep2.setStyleSheet(f"background:{COLORS['border']};")
        draw_row.addWidget(sep2)

        # Zoom controls
        btn_zoom_out = QPushButton("−")
        btn_zoom_out.setToolTip("Zoom out")
        btn_zoom_out.setFixedHeight(26)
        btn_zoom_out.clicked.connect(self._zoom_out)
        draw_row.addWidget(btn_zoom_out)

        self._zoom_label = QLabel("100%")
        draw_row.addWidget(self._zoom_label)

        btn_zoom_in = QPushButton("+")
        btn_zoom_in.setToolTip("Zoom in")
        btn_zoom_in.setFixedHeight(26)
        btn_zoom_in.clicked.connect(self._zoom_in)
        draw_row.addWidget(btn_zoom_in)

        btn_center = QPushButton("⊙")
        btn_center.setToolTip("Centre view on objects (100% zoom)")
        btn_center.setFixedHeight(26)
        btn_center.clicked.connect(lambda: self._canvas.fit_to_contents())
        draw_row.addWidget(btn_center)

        sep3 = QFrame()
        sep3.setFixedSize(1, 22)
        sep3.setStyleSheet(f"background:{COLORS['border']};")
        draw_row.addWidget(sep3)

        btn_reset = QPushButton("Reset")
        btn_reset.setToolTip("Reset canvas to given objects")
        btn_reset.setFixedHeight(26)
        btn_reset.clicked.connect(self._reset_canvas)
        draw_row.addWidget(btn_reset)

        sep_snap = QFrame()
        sep_snap.setFixedSize(1, 22)
        sep_snap.setStyleSheet(f"background:{COLORS['border']};")
        draw_row.addWidget(sep_snap)

        snap_label = QLabel("Snap")
        snap_label.setStyleSheet(
            f"color:{COLORS['textSecondary']}; font-size:11px;")
        draw_row.addWidget(snap_label)

        self._snap_toggle = ToggleSwitch(checked=True)
        self._snap_toggle.setToolTip(
            "Toggle snap to circle / line / intersection")
        self._snap_toggle.set_toggled_callback(self._toggle_snap)
        draw_row.addWidget(self._snap_toggle)

        draw_inner.setFixedSize(draw_inner.sizeHint())

        draw_scroll = QScrollArea()
        draw_scroll.setWidget(draw_inner)
        draw_scroll.setWidgetResizable(False)
        draw_scroll.setVerticalScrollBarPolicy(
            Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        draw_scroll.setHorizontalScrollBarPolicy(
            Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        draw_scroll.setFixedHeight(draw_inner.sizeHint().height() + 8)
        draw_scroll.setStyleSheet(
            f"QScrollArea {{ border:none; background:{COLORS['background']};"
            f" border-bottom:1px solid {COLORS['border']}; }}"
            " QScrollBar:horizontal { height:6px; }"
            " QScrollBar::handle:horizontal { background:#b0b0b0;"
            "   border-radius:3px; min-width:30px; }"
            " QScrollBar::add-line, QScrollBar::sub-line { width:0px; }"
        )
        canvas_vbox.addWidget(draw_scroll)

        # ── Color picker row ──────────────────────────────────────────
        color_bar = QFrame()
        color_bar.setFixedHeight(32)
        color_bar.setStyleSheet(f"QFrame {{ background: {COLORS['surface']}; border-bottom: 1px solid {COLORS['border']}; }}")
        cl = QHBoxLayout(color_bar)
        cl.setContentsMargins(12, 2, 12, 2)
        cl.setSpacing(4)
        color_label = QLabel("Color:")
        color_label.setStyleSheet("font-size: 12px;")
        cl.addWidget(color_label)
        self._color_btns: list[QPushButton] = []
        for i, qc in enumerate(COLOR_PALETTE):
            btn = QPushButton()
            btn.setFixedSize(22, 22)
            hex_str = qc.name()
            btn.setStyleSheet(
                f"background: {hex_str}; border: 2px solid {'#2d70b3' if i == 0 else 'transparent'}; border-radius: 11px;"
            )
            btn.clicked.connect(lambda checked, idx=i: self._pick_color(idx))
            cl.addWidget(btn)
            self._color_btns.append(btn)
        cl.addStretch()
        canvas_vbox.addWidget(color_bar)

        # ── Splitter: canvas | proof panel | (reference/translation tabs) ─
        splitter = QSplitter(Qt.Orientation.Horizontal)
        self._canvas = CanvasWidget()
        self._canvas.zoom_changed = self._update_zoom_label
        self._proof_panel = ProofPanel()
        self._dirty = False
        # Canvas changes reset proof evaluations back to ? (v1.14.0)
        self._canvas.scene.canvas_changed.connect(self._proof_panel.reset_evaluations)
        self._canvas.scene.canvas_changed.connect(self._mark_dirty)
        self._proof_panel.step_changed.connect(self._mark_dirty)
        canvas_vbox.addWidget(self._canvas)
        body_splitter.addWidget(canvas_container)
        body_splitter.addWidget(self._proof_panel)

        # Right sidebar: Rule Reference panel (hidden by default)
        self._ref_panel = RuleReferencePanel()
        self._ref_panel.setMinimumWidth(300)
        self._ref_panel.setMaximumWidth(460)
        self._ref_panel.setVisible(False)
        body_splitter.addWidget(self._ref_panel)

        body_splitter.setStretchFactor(0, 3)
        body_splitter.setStretchFactor(1, 2)
        body_splitter.setStretchFactor(2, 1)
        self._body_splitter = body_splitter
        self._splitter_saved_sizes = [0, 0, 0]

        layout.addWidget(body_splitter)
        body_splitter.splitterMoved.connect(self._on_splitter_moved)

        # ── Floating restore tabs (overlay, not in any layout) ────────
        _tab_style = (
            f"QPushButton{{background:{COLORS['surface']};"
            f"color:{COLORS['primary']};"
            f"border:1px solid {COLORS['border']};"
            "border-radius:3px;font-size:14px;padding:0px;}}"
            f"QPushButton:hover{{background:{COLORS['primary']};color:white;}}"
        )
        self._left_tab = QPushButton("\u25b6", self)
        self._left_tab.setToolTip("Show canvas")
        self._left_tab.setFixedSize(20, 60)
        self._left_tab.setCursor(Qt.CursorShape.PointingHandCursor)
        self._left_tab.setStyleSheet(_tab_style)
        self._left_tab.setVisible(False)
        self._left_tab.clicked.connect(lambda: self._restore_panel(0))
        self._left_tab.raise_()

        self._right_tab = QPushButton("\u25c0", self)
        self._right_tab.setToolTip("Show proof panel")
        self._right_tab.setFixedSize(20, 60)
        self._right_tab.setCursor(Qt.CursorShape.PointingHandCursor)
        self._right_tab.setStyleSheet(_tab_style)
        self._right_tab.setVisible(False)
        self._right_tab.clicked.connect(lambda: self._restore_panel(1))
        self._right_tab.raise_()

        self._right_tab2 = QPushButton("\u25c0", self)
        self._right_tab2.setToolTip("Show reference panel")
        self._right_tab2.setFixedSize(20, 60)
        self._right_tab2.setCursor(Qt.CursorShape.PointingHandCursor)
        self._right_tab2.setStyleSheet(_tab_style)
        self._right_tab2.setVisible(False)
        self._right_tab2.clicked.connect(lambda: self._restore_panel(2))
        self._right_tab2.raise_()

    # ── Splitter collapse / restore ─────────────────────────────────

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._reposition_restore_tabs()

    def _reposition_restore_tabs(self):
        """Move the floating restore tabs to the correct edge positions."""
        if not hasattr(self, '_body_splitter'):
            return
        sp = self._body_splitter
        sp_geo = sp.geometry()
        cy = sp_geo.y() + sp_geo.height() // 2 - 30  # vertical center

        # Left tab: left edge of splitter
        self._left_tab.move(sp_geo.x(), cy)
        self._left_tab.raise_()

        # Right tab: right edge of splitter
        self._right_tab.move(sp_geo.x() + sp_geo.width() - 20, cy)
        self._right_tab.raise_()

        # Right tab 2 (reference): just left of right_tab when both visible
        if self._right_tab.isVisible() and self._right_tab2.isVisible():
            self._right_tab2.move(
                sp_geo.x() + sp_geo.width() - 20, cy - 65)
        else:
            self._right_tab2.move(
                sp_geo.x() + sp_geo.width() - 20, cy)
        self._right_tab2.raise_()

    def _on_splitter_moved(self, pos, index):
        sizes = self._body_splitter.sizes()
        total = sum(sizes)
        if total <= 0:
            return
        # Save sizes whenever all visible panels have reasonable width
        if all(s > 30 for s in sizes if s > 0) and sizes[0] > 30 and sizes[1] > 30:
            self._splitter_saved_sizes = list(sizes)
        # Canvas collapsed (pushed all the way left)
        self._left_tab.setVisible(sizes[0] < 10)
        # Proof panel collapsed (pushed all the way right)
        self._right_tab.setVisible(sizes[1] < 10)
        # Reference panel collapsed (only when it was visible)
        if self._ref_panel.isVisible():
            self._right_tab2.setVisible(sizes[2] < 10)
        else:
            self._right_tab2.setVisible(False)
        self._reposition_restore_tabs()

    def _restore_panel(self, panel_index):
        saved = self._splitter_saved_sizes
        sizes = self._body_splitter.sizes()
        total = sum(sizes)
        if total <= 0:
            return
        if panel_index == 2 and not self._ref_panel.isVisible():
            # Reference panel was hidden via toggle button, re-show it
            self._ref_panel.setVisible(True)
            self._btn_ref.setChecked(True)
        target_size = saved[panel_index] if saved[panel_index] > 50 else total // 3
        sizes[panel_index] = target_size
        remaining = total - target_size
        other_indices = [i for i in range(3) if i != panel_index]
        other_total = sum(sizes[i] for i in other_indices)
        if other_total > 0:
            r = remaining / other_total
            sizes[other_indices[0]] = int(sizes[other_indices[0]] * r)
            sizes[other_indices[1]] = total - sizes[panel_index] - sizes[other_indices[0]]
        else:
            sizes[other_indices[0]] = remaining
            sizes[other_indices[1]] = 0
        self._body_splitter.setSizes(sizes)
        self._left_tab.setVisible(sizes[0] < 10)
        self._right_tab.setVisible(sizes[1] < 10)
        if self._ref_panel.isVisible():
            self._right_tab2.setVisible(sizes[2] < 10)
        else:
            self._right_tab2.setVisible(False)
        self._reposition_restore_tabs()

    def load_proposition(self, prop: Proposition):
        self._current_prop = prop
        self._title_label.setText(f"{prop.name} — {prop.title}")
        self._canvas.clear()
        self._proof_panel.clear()
        # Set the proof name from the proposition
        self._proof_panel.set_proof_name(
            prop.e_library_name or prop.name)
        # Block canvas_changed signals during batch load to avoid
        # mid-rebuild calls into the proof panel.
        self._canvas._scene.blockSignals(True)
        try:
            self._load_given_objects(prop)
        finally:
            self._canvas._scene.blockSignals(False)
        # Auto-populate declarations from given objects
        if prop.given_objects:
            pt_labels = [pt["label"] for pt in prop.given_objects.points]
            self._proof_panel.set_declarations(pt_labels, [])

        # Phase 9.1: Source premises and conclusion from E library when
        # available, falling back to given-object heuristics for
        # non-Euclid entries.
        e_thm = prop.get_e_theorem()
        if e_thm is not None:
            for hyp in e_thm.sequent.hypotheses:
                self._proof_panel.add_premise_text(str(hyp))
            if e_thm.sequent.conclusions:
                goal = ", ".join(str(c) for c in e_thm.sequent.conclusions)
                self._proof_panel.set_conclusion(goal)
            elif prop.conclusion_predicate:
                self._proof_panel.set_conclusion(prop.conclusion_predicate)
        else:
            # Fallback: generate System E premises from given objects
            formal_premises = self._build_formal_premises(prop)
            for fp in formal_premises:
                self._proof_panel.add_premise_text(fp)
            goal_text = prop.conclusion_predicate or prop.conclusion
            if goal_text:
                self._proof_panel.set_conclusion(goal_text)

        self._dirty = False

    @staticmethod
    def _build_formal_premises(prop: Proposition):
        """Generate System E premises from given objects (fallback).

        Used only when the proposition has no E library entry.
        Uses System E syntax: ¬(a = b) for distinct points,
        on(a, L) for incidence, etc.
        """
        premises = []
        if prop.given_objects:
            labels = [pt["label"] for pt in prop.given_objects.points]
            # Distinct-point assertions for segments
            for seg in prop.given_objects.segments:
                a, b = seg["from"], seg["to"]
                premises.append(f"¬({a} = {b})")
            # Circle constructions
            for circ in prop.given_objects.circles:
                c, r = circ["center"], circ["radius"]
                premises.append(f"¬({c} = {r})")
        return premises

    def _load_given_objects(self, prop: Proposition):
        if prop.given_objects:
            for pt in prop.given_objects.points:
                self._canvas.add_point(pt["label"], pt["x"], pt["y"])
            for seg in prop.given_objects.segments:
                self._canvas.add_segment(seg["from"], seg["to"])
            for circ in prop.given_objects.circles:
                self._canvas.add_circle(circ["center"], circ["radius"])
            for am in prop.given_objects.angle_marks:
                self._canvas.scene.add_angle_mark(
                    am["from"], am["vertex"], am["to"],
                    is_right=am.get("is_right", False),
                )

    def _mark_dirty(self):
        self._dirty = True

    def _new_blank_proof(self):
        """Start a blank proof, prompting to save if dirty."""
        if self._dirty:
            reply = QMessageBox.question(
                self, "Unsaved Changes",
                "Save before starting a new proof?",
                QMessageBox.StandardButton.Save
                | QMessageBox.StandardButton.Discard
                | QMessageBox.StandardButton.Cancel,
            )
            if reply == QMessageBox.StandardButton.Save:
                self._save()
            elif reply == QMessageBox.StandardButton.Cancel:
                return
        self._mw.open_blank()


    def _pick_color(self, idx: int):
        from .canvas_widget import COLOR_PALETTE
        for i, btn in enumerate(self._color_btns):
            hex_str = COLOR_PALETTE[i].name()
            border = '#2d70b3' if i == idx else 'transparent'
            btn.setStyleSheet(
                f"background: {hex_str}; border: 2px solid {border}; border-radius: 11px;"
            )
        self._canvas.set_draw_color(COLOR_PALETTE[idx])

    def _reset_canvas(self):
        """Reset canvas to the proposition's given objects."""
        self._canvas.clear()
        if self._current_prop:
            self._load_given_objects(self._current_prop)
            QTimer.singleShot(50, self._canvas.fit_to_contents)

    def _toggle_snap(self, enabled: bool):
        """Toggle snap-to-circle/line/intersection on the canvas."""
        self._canvas.scene._snap_enabled = enabled

    def _set_tool(self, tid: str):
        for name, btn in self._tools.items():
            btn.setChecked(name == tid)
        self._canvas.set_tool(tid)

    def _set_tool_btn(self, tid: str):
        self._set_tool(tid)

    def _zoom_in(self):
        self._canvas.zoom_in()
        self._update_zoom_label()

    def _zoom_out(self):
        self._canvas.zoom_out()
        self._update_zoom_label()

    def _update_zoom_label(self):
        self._zoom_label.setText(f"{self._canvas.zoom_percent()}%")

    def _save(self):
        """Prompt: Canvas Only (.euclid), Canvas + Proof (.euclid), Proof Only (.json), or Cancel."""
        msg = QMessageBox(self)
        msg.setStyleSheet(
            "QMessageBox { background-color: white; }"
            " QLabel { color: #1a1a2e; background: transparent; }"
            " QPushButton { background: white; color: #1a1a2e;"
            "   border: 1px solid #c0c8d4; border-radius: 4px;"
            "   padding: 6px 16px; font-size: 12px; }"
            " QPushButton:hover { background: #f0f4ff;"
            "   border-color: #2d70b3; }")
        msg.setWindowTitle("Save")
        msg.setText("What would you like to save?")
        msg.setInformativeText(
            "Canvas Only (.euclid) — diagram only, no proof journal\n"
            "Canvas + Proof (.euclid) — full workspace\n"
            "Proof Only (.euclid) — proof journal only, no canvas")
        btn_canvas = msg.addButton("Canvas Only", QMessageBox.ButtonRole.AcceptRole)
        btn_both = msg.addButton("Canvas + Proof", QMessageBox.ButtonRole.AcceptRole)
        btn_proof = msg.addButton("Proof Only", QMessageBox.ButtonRole.AcceptRole)
        msg.addButton(QMessageBox.StandardButton.Cancel)
        msg.exec()
        clicked = msg.clickedButton()
        if clicked == btn_canvas:
            self._save_euclid(include_journal=False)
        elif clicked == btn_both:
            self._save_euclid(include_journal=True)
        elif clicked == btn_proof:
            self._save_proof_json()

    def _save_euclid(self, include_journal: bool = True):
        """Save a .euclid file, optionally including the proof journal."""
        path, _ = QFileDialog.getSaveFileName(
            self, "Save Euclid File", "", "Euclid Files (*.euclid)")
        if path:
            canvas = self._canvas.get_state()
            journal = self._proof_panel.get_journal_state() if include_journal else None
            save_proof(path, canvas, journal)
            self._dirty = False
            self._set_file_title(path)
            label = "canvas + proof" if include_journal else "canvas"
            self._mw.statusBar().showMessage(f"Saved {label} to {path}")

    def _save_proof_json(self):
        """Save proof journal only as a .euclid file."""
        path, _ = QFileDialog.getSaveFileName(
            self, "Save Proof File", "", "Euclid Files (*.euclid)")
        if path:
            journal = self._proof_panel.get_journal_state()
            save_journal_json(path, journal)
            self._dirty = False
            self._set_file_title(path)
            self._mw.statusBar().showMessage(f"Saved proof to {path}")

    def _toggle_reference(self):
        """Show or hide the reference / translation sidebar."""
        visible = not self._ref_panel.isVisible()
        self._ref_panel.setVisible(visible)
        self._btn_ref.setChecked(visible)
        # Hide the reference restore tab when the panel is toggled off
        if not visible:
            self._right_tab2.setVisible(False)
        self._reposition_restore_tabs()

    def _import(self):
        dlg = _OpenFileDialog(self)
        if dlg.exec() == QDialog.DialogCode.Accepted and dlg.selected_path:
            self._import_file(dlg.selected_path)

    def _import_file(self, path: str):
        """Load a .euclid file by path."""
        fmt = detect_file_format(path)
        self._set_file_title(path)
        if fmt == "euclid-journal":
            journal = load_journal_json(path)
            self._proof_panel.clear()
            self._proof_panel.restore_journal_state(journal)
            self._mw.statusBar().showMessage(f"Loaded proof from {path}")
        else:
            data = load_proof(path)
            self._load_canvas_from_data(data)
            if data.get("has_journal"):
                journal = data.get("journal", {})
                self._proof_panel.clear()
                self._proof_panel.restore_journal_state(journal)
                self._mw.statusBar().showMessage(
                    f"Loaded canvas + proof from {path}")
            else:
                self._mw.statusBar().showMessage(
                    f"Loaded canvas from {path} (proof journal unchanged)")
        self._dirty = False
        QTimer.singleShot(50, self._canvas.fit_to_contents)

    def _load_canvas_from_data(self, data: dict):
        """Replace the canvas with objects from a deserialized .euclid dict."""
        self._canvas.clear()
        self._canvas._scene.blockSignals(True)
        try:
            for pt in data.get("points", []):
                self._canvas.add_point(pt["label"], pt["x"], pt["y"])
            for seg in data.get("segments", []):
                s = self._canvas.scene.add_segment(seg["from"], seg["to"])
                if s and seg.get("color"):
                    from PyQt6.QtGui import QColor, QPen
                    s.draw_color = QColor(seg["color"])
                    s.setPen(QPen(s.draw_color, 2))
            for ray in data.get("rays", []):
                r = self._canvas.scene.add_ray(
                    ray["from"], ray["through"])
                if r and ray.get("color"):
                    from PyQt6.QtGui import QColor, QPen
                    from PyQt6.QtCore import Qt
                    r.draw_color = QColor(ray["color"])
                    pen = QPen(r.draw_color, 1.5)
                    pen.setStyle(Qt.PenStyle.DotLine)
                    r.setPen(pen)
            for circ in data.get("circles", []):
                rp = circ.get("radius_point")
                if rp:
                    c = self._canvas.scene.add_circle_by_radius_pt(
                        circ["center"], rp)
                else:
                    c = self._canvas.scene.add_circle(
                        circ["center"], circ["radius"])
                if c and circ.get("color"):
                    from PyQt6.QtGui import QColor, QPen
                    c.draw_color = QColor(circ["color"])
                    c.setPen(QPen(c.draw_color, 2))
            for am in data.get("angle_marks", []):
                self._canvas.scene.add_angle_mark(
                    am["from"], am["vertex"], am["to"],
                    is_right=am.get("is_right", False))
            for tc, pairs in data.get("equality_groups", []):
                self._canvas.scene._equality_groups.append((tc, pairs))
            self._canvas.scene._apply_equality_ticks()
        finally:
            self._canvas._scene.blockSignals(False)

    def _set_file_title(self, path: str):
        """Update the toolbar title and proof name from a file path."""
        import os
        name = os.path.splitext(os.path.basename(path))[0]
        self._title_label.setText(name)
        self._proof_panel.set_proof_name(name)
