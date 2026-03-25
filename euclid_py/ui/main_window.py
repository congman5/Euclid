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


def _load_user_bookmarks() -> dict:
    """Load saved custom folders/files and dialog geometry from disk."""
    path = _user_bookmarks_path()
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            # Migrate old list format → dict
            if isinstance(data, list):
                return {"bookmarks": data}
            return data
        except Exception:
            pass
    return {"bookmarks": []}


def _save_user_bookmarks(data: dict):
    """Persist custom folders/files and dialog geometry to disk."""
    path = _user_bookmarks_path()
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except Exception:
        pass


import re as _re
import unicodedata as _ud


def _clean_emoji(text: str) -> str:
    """Strip invisible variation selectors / ZWJ / formatting chars that
    render as boxes in Qt, keeping just the visible emoji glyph.
    If multiple visible glyphs remain, keep only the last one (the user's
    most recent pick)."""
    # Remove variation selectors (U+FE00–U+FE0F), ZWJ (U+200D),
    # combining enclosing keycaps (U+20E3), and other invisible format chars
    # that the Windows emoji picker appends.
    cleaned = []
    for ch in text:
        cat = _ud.category(ch)
        # Keep visible characters; skip Mn (non-spacing mark), Me (enclosing
        # mark), Cf (format), and specific variation selectors
        if cat in ("Mn", "Cf") or 0xFE00 <= ord(ch) <= 0xFE0F:
            continue
        cleaned.append(ch)
    # If multiple visible glyphs remain, keep only the last one
    # (the user's most recent pick). Use list() which handles surrogates.
    result = "".join(cleaned)
    codepoints = list(result)
    if len(codepoints) > 1:
        # Keep the last codepoint (the emoji the user just selected)
        result = codepoints[-1]
    return result or text[:1]


def _natural_sort_key(filename: str):
    """Sort key that orders numbers numerically: I.2 before I.10."""
    parts = _re.split(r'(\d+)', filename)
    return [int(p) if p.isdigit() else p.lower() for p in parts]


# White-theme base stylesheet applied to the entire open dialog to
# override any dark-theme inheritance from the main window.
_DIALOG_BASE_STYLE = """
    QDialog { background: white; }
    QWidget { background: white; color: #1a1a2e; }
    QLabel { color: #1a1a2e; background: transparent; }
    QPushButton { color: #1a1a2e; background: white; }
    QListWidget { background: white; color: #1a1a2e; }
    QListWidget::item { color: #1a1a2e; }
    QMenu { background: white; color: #1a1a2e;
            border: 1px solid #d0d4da; border-radius: 4px; padding: 4px; }
    QMenu::item { padding: 6px 20px; color: #1a1a2e; }
    QMenu::item:selected { background: #edf2ff; color: #1a1a2e; }
    QMenu::item:disabled { color: #aaa; }
    QMenu::separator { height: 1px; background: #e5e7eb; margin: 4px 8px; }
    QInputDialog { background: white; }
    QInputDialog QLabel { color: #1a1a2e; }
    QInputDialog QLineEdit { background: white; color: #1a1a2e;
                              border: 1px solid #d0d4da; border-radius: 4px;
                              padding: 4px 8px; }
    QMessageBox { background: white; }
    QMessageBox QLabel { color: #1a1a2e; }
"""


class _DropFileList(QListWidget):
    """File list that supports dropping items onto folder rows to move them."""

    _ROLE_PATH = Qt.ItemDataRole.UserRole
    _ROLE_IS_FOLDER = Qt.ItemDataRole.UserRole + 1

    # Signal: file_path was dropped onto folder_path
    from PyQt6.QtCore import pyqtSignal
    fileDroppedOnFolder = pyqtSignal(str, str)  # (source_path, target_folder)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptDrops(True)
        self._drop_target_item = None
        # Cache of file paths being dragged — selectedItems() may be empty
        # after Qt processes the drag, so we snapshot at drag start
        self.dragged_paths: list[str] = []

    def startDrag(self, supportedActions):
        """Snapshot selected file paths before Qt clears the selection."""
        self.dragged_paths = []
        for sel in self.selectedItems():
            p = sel.data(self._ROLE_PATH)
            is_folder = sel.data(self._ROLE_IS_FOLDER)
            if p and not is_folder:
                self.dragged_paths.append(p)
        super().startDrag(supportedActions)

    def dragEnterEvent(self, event):
        # Accept both internal moves and drops from the sidebar
        if event.source() is self or isinstance(event.source(), QListWidget):
            event.acceptProposedAction()
        else:
            super().dragEnterEvent(event)

    def dragMoveEvent(self, event):
        # Highlight the folder item under the cursor
        item = self.itemAt(event.position().toPoint())
        old = self._drop_target_item

        if item and item.data(self._ROLE_IS_FOLDER):
            if old and old is not item:
                old.setBackground(QColor("transparent"))
            item.setBackground(QColor("#dce8f7"))
            self._drop_target_item = item
            event.acceptProposedAction()
        else:
            if old:
                old.setBackground(QColor("transparent"))
                self._drop_target_item = None
            # Allow normal internal reorder when not over a folder
            super().dragMoveEvent(event)

    def dropEvent(self, event):
        # Clear highlight
        if self._drop_target_item:
            self._drop_target_item.setBackground(QColor("transparent"))

        target_item = self.itemAt(event.position().toPoint())

        if target_item and target_item.data(self._ROLE_IS_FOLDER):
            target_folder = target_item.data(self._ROLE_PATH)
            source = event.source()

            if source is self:
                # Dropping a file-list item onto a folder within the same list
                for sel in self.selectedItems():
                    src_path = sel.data(self._ROLE_PATH)
                    if src_path and not sel.data(self._ROLE_IS_FOLDER):
                        self.fileDroppedOnFolder.emit(src_path, target_folder)
            elif isinstance(source, QListWidget):
                # Dropping from the sidebar
                for sel in source.selectedItems():
                    sb_idx = sel.data(Qt.ItemDataRole.UserRole + 10)
                    if sb_idx is not None:
                        # Pass the sidebar index via a property so the
                        # dialog can look up the path
                        self.fileDroppedOnFolder.emit(
                            f"__sb__{sb_idx}", target_folder)
            event.acceptProposedAction()
        else:
            # Normal internal reorder
            super().dropEvent(event)
            self._drop_target_item = None

    def dragLeaveEvent(self, event):
        if self._drop_target_item:
            self._drop_target_item.setBackground(QColor("transparent"))
            self._drop_target_item = None
        super().dragLeaveEvent(event)


class _DropSidebar(QListWidget):
    """Sidebar that accepts drops from the file list AND internal sidebar
    file entries onto folder entries."""

    from PyQt6.QtCore import pyqtSignal
    fileDroppedOnSidebarFolder = pyqtSignal(str, str)  # (source_path, target_folder)
    # Emitted when a sidebar file entry is dropped onto a sidebar folder entry
    sidebarFileToFolder = pyqtSignal(int, int)  # (source_sb_idx, target_sb_idx)
    # Emitted when a file from the file list is dropped onto empty sidebar space
    addToQuickAccess = pyqtSignal(str)  # file_path

    _ROLE_SB_INDEX = Qt.ItemDataRole.UserRole + 10

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptDrops(True)
        self._drop_target_item = None
        # Callback set by the dialog to check if a sb_idx is a folder
        self._is_folder_cb = None  # type: Callable[[int], bool] | None

    def _is_folder_entry(self, item):
        """Check if a sidebar item represents a folder."""
        if not item:
            return False
        sb_idx = item.data(self._ROLE_SB_INDEX)
        if sb_idx is None:
            return False
        if self._is_folder_cb:
            return self._is_folder_cb(sb_idx)
        return True  # fallback: assume yes

    def dragEnterEvent(self, event):
        if isinstance(event.source(), QListWidget):
            event.acceptProposedAction()
        else:
            super().dragEnterEvent(event)

    def _dragged_is_file(self):
        """Check if the currently dragged sidebar item is a file (not folder)."""
        item = self.currentItem()
        if not item:
            return False
        sb_idx = item.data(self._ROLE_SB_INDEX)
        if sb_idx is None:
            return False
        # A file entry is one that is NOT a folder
        if self._is_folder_cb:
            return not self._is_folder_cb(sb_idx)
        return False

    def dragMoveEvent(self, event):
        item = self.itemAt(event.position().toPoint())
        old = self._drop_target_item
        dragged = self.currentItem()
        source = event.source()

        # Only show folder-drop highlight when dragging a file onto a folder
        # (not when reordering sidebar entries)
        show_folder_drop = (
            item
            and item is not dragged
            and self._is_folder_entry(item)
            and (source is not self or self._dragged_is_file())
        )

        if show_folder_drop:
            if old and old is not item:
                old.setBackground(QColor("transparent"))
            item.setBackground(QColor("#dce8f7"))
            self._drop_target_item = item
            event.acceptProposedAction()
        else:
            if old:
                old.setBackground(QColor("transparent"))
                self._drop_target_item = None
            # Accept external drops anywhere (add to Quick Access)
            if source is not None and source is not self:
                event.acceptProposedAction()
            else:
                super().dragMoveEvent(event)

    def dropEvent(self, event):
        if self._drop_target_item:
            self._drop_target_item.setBackground(QColor("transparent"))

        target_item = self.itemAt(event.position().toPoint())
        source = event.source()

        # Only handle file-to-folder drops, not folder reordering
        if target_item and self._is_folder_entry(target_item):
            target_sb_idx = target_item.data(self._ROLE_SB_INDEX)

            if source is self and self._dragged_is_file():
                # Internal sidebar drag: file entry dropped onto folder entry
                for sel in self.selectedItems():
                    src_sb_idx = sel.data(self._ROLE_SB_INDEX)
                    if src_sb_idx is not None and src_sb_idx != target_sb_idx:
                        self.sidebarFileToFolder.emit(
                            src_sb_idx, target_sb_idx)
                event.acceptProposedAction()
                self._drop_target_item = None
                return
            elif source is not None and source is not self:
                # Drop from file list onto sidebar folder
                # Use cached dragged_paths since selectedItems() may be empty
                paths = getattr(source, 'dragged_paths', [])
                if not paths:
                    # Fallback to selectedItems
                    for sel in source.selectedItems():
                        p = sel.data(Qt.ItemDataRole.UserRole)
                        if p and not sel.data(Qt.ItemDataRole.UserRole + 1):
                            paths.append(p)
                for src_path in paths:
                    self.fileDroppedOnSidebarFolder.emit(
                        src_path, f"__sb__{target_sb_idx}")
                event.acceptProposedAction()
                self._drop_target_item = None
                return

        # Drop from file list onto empty space / non-folder entry
        # → add as Quick Access bookmark
        if source is not None and source is not self:
            paths = list(getattr(source, 'dragged_paths', []))
            if not paths:
                for sel in source.selectedItems():
                    p = sel.data(Qt.ItemDataRole.UserRole)
                    if p:
                        paths.append(p)
            for src_path in paths:
                self.addToQuickAccess.emit(src_path)
            event.acceptProposedAction()
            self._drop_target_item = None
            return

        # Normal internal reorder (folders and entries repositioning)
        super().dropEvent(event)
        self._drop_target_item = None

    def dragLeaveEvent(self, event):
        if self._drop_target_item:
            self._drop_target_item.setBackground(QColor("transparent"))
            self._drop_target_item = None
        super().dragLeaveEvent(event)


class _OpenFileDialog(QDialog):
    """Custom file-open dialog with sidebar, folders-as-features,
    drag-drop reorder, drag into folders, and delete with confirmation."""

    _ROLE_PATH = Qt.ItemDataRole.UserRole
    _ROLE_IS_FOLDER = Qt.ItemDataRole.UserRole + 1

    # ── Small button stylesheet (reused) ──────────────────────────
    _SM_BTN = (
        "QPushButton { padding: 5px 10px; border: 1px solid #c0c8d4;"
        " border-radius: 4px; background: white;"
        " color: #1a1a2e; font-size: 11px; }"
        " QPushButton:hover { background: #f0f4ff; }"
    )

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Open Proof File")
        self.resize(760, 560)
        self.setStyleSheet(_DIALOG_BASE_STYLE)
        self.selected_path: str | None = None

        from ..resources import resource_path
        self._unsolved_dir = resource_path("unsolved_proofs")
        self._solved_dir = resource_path("solved_proofs")
        self._prefs = _load_user_bookmarks()
        self._bookmarks = self._prefs.get("bookmarks", [])
        self._nav_stack: list[str] = []  # for "Back" navigation

        root = QHBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        # ── Left sidebar ─────────────────────────────────────────────
        sidebar = QFrame()
        sidebar.setFixedWidth(200)
        sidebar.setStyleSheet(
            "QFrame { background: #fafbfc;"
            " border-right: 1px solid #e5e7eb; }")
        sb_outer = QVBoxLayout(sidebar)
        sb_outer.setContentsMargins(8, 12, 8, 12)
        sb_outer.setSpacing(4)

        sb_title = QLabel("Quick Access")
        sb_title.setFont(QFont("Segoe UI", 11, QFont.Weight.Bold))
        sb_title.setStyleSheet(
            "color: #1a1a2e; border: none; padding: 0 0 6px 4px;"
            " background: transparent;")
        sb_outer.addWidget(sb_title)

        # Sidebar list — draggable, right-clickable, accepts drops from file list
        self._sb_list = _DropSidebar()
        self._sb_list.setDragDropMode(QListWidget.DragDropMode.InternalMove)
        self._sb_list.setDefaultDropAction(Qt.DropAction.MoveAction)
        # Tell the sidebar how to check if an entry is a folder
        self._sb_list._is_folder_cb = self._sb_idx_is_folder
        self._sb_list.setStyleSheet("""
            QListWidget {
                border: none; background: transparent;
                outline: none; font-size: 12px; color: #1a1a2e;
                font-family: 'Segoe UI Emoji', 'Segoe UI', sans-serif;
            }
            QListWidget::item {
                padding: 8px 10px; border-radius: 4px;
                color: #1a1a2e;
            }
            QListWidget::item:hover {
                background: #edf2ff;
            }
            QListWidget::item:selected {
                background: #dce8f7; color: #1a1a2e;
            }
        """)
        self._sb_list.clicked.connect(self._on_sidebar_click)
        self._sb_list.setContextMenuPolicy(
            Qt.ContextMenuPolicy.CustomContextMenu)
        self._sb_list.customContextMenuRequested.connect(
            self._show_sidebar_context_menu)
        self._sb_list.model().rowsMoved.connect(self._on_sidebar_reordered)
        sb_outer.addWidget(self._sb_list, stretch=1)

        # Populate sidebar — built-in + user bookmarks
        self._sb_entries: list[dict] = []  # {path, name, icon, removable}

        self._sb_entries.append({
            "path": self._unsolved_dir,
            "name": "Unsolved Proofs",
            "icon": "\u25B6",
            "removable": False,
        })
        self._sb_entries.append({
            "path": self._solved_dir,
            "name": "Solved Proofs",
            "icon": "\u2713",
            "removable": False,
        })
        for bm in self._bookmarks:
            raw_icon = bm.get("icon", "\u25B8"
                              if bm.get("type") != "file" else "\u2022")
            self._sb_entries.append({
                "path": bm.get("path", ""),
                "name": bm.get("name", ""),
                "icon": _clean_emoji(raw_icon),
                "removable": True,
            })
        self._rebuild_sidebar()

        # Sidebar bottom buttons — compact row
        sb_btn_row = QHBoxLayout()
        sb_btn_row.setSpacing(4)
        btn_add_folder = QPushButton("+ Folder")
        btn_add_folder.setStyleSheet(self._SM_BTN)
        btn_add_folder.setToolTip("Create a new folder in Quick Access")
        btn_add_folder.clicked.connect(self._create_sidebar_folder)
        sb_btn_row.addWidget(btn_add_folder)
        btn_add_file = QPushButton("+ File")
        btn_add_file.setStyleSheet(self._SM_BTN)
        btn_add_file.setToolTip("Add a single file to the sidebar")
        btn_add_file.clicked.connect(self._add_file_bookmark)
        sb_btn_row.addWidget(btn_add_file)
        sb_outer.addLayout(sb_btn_row)

        root.addWidget(sidebar)

        # ── Right content — file list ────────────────────────────────
        right = QWidget()
        right.setStyleSheet("background: white;")
        rl = QVBoxLayout(right)
        rl.setContentsMargins(12, 12, 12, 12)
        rl.setSpacing(8)

        # Toolbar row: back button, folder label, new folder, delete
        toolbar_row = QHBoxLayout()
        toolbar_row.setSpacing(6)

        self._back_btn = QPushButton("\u2190")
        self._back_btn.setFixedSize(28, 28)
        self._back_btn.setStyleSheet(
            "QPushButton { border: 1px solid #d0d4da; border-radius: 4px;"
            " background: white; color: #1a1a2e; font-size: 14px; }"
            " QPushButton:hover { background: #f0f4ff; }")
        self._back_btn.setToolTip("Go back")
        self._back_btn.clicked.connect(self._go_back)
        self._back_btn.setVisible(False)  # Hidden until we navigate into a subfolder
        toolbar_row.addWidget(self._back_btn)

        self._folder_label = QLabel("")
        self._folder_label.setFont(QFont("Segoe UI", 12, QFont.Weight.Bold))
        self._folder_label.setStyleSheet(
            "color: #1a1a2e; background: transparent;")
        toolbar_row.addWidget(self._folder_label, stretch=1)

        rl.addLayout(toolbar_row)

        # File list — with drag & drop onto folders
        self._file_list = _DropFileList()
        self._file_list.setDragDropMode(QListWidget.DragDropMode.InternalMove)
        self._file_list.setDefaultDropAction(Qt.DropAction.MoveAction)
        self._file_list.setSelectionMode(
            QListWidget.SelectionMode.ExtendedSelection)
        self._file_list.setIconSize(QSize(0, 0))  # Hide empty icon area
        self._file_list.setStyleSheet("""
            QListWidget {
                border: 1px solid #e5e7eb;
                border-radius: 6px;
                background: white;
                outline: none;
                font-size: 13px;
                color: #1a1a2e;
            }
            QListWidget::item {
                padding: 10px 14px;
                border-bottom: 1px solid #f0f0f0;
                color: #1a1a2e;
            }
            QListWidget::item:hover {
                background: #f5f8ff;
                color: #1a1a2e;
            }
            QListWidget::item:selected {
                background: #dce8f7;
                color: #2d70b3;
            }
            QListWidget::indicator {
                width: 0px;
                height: 0px;
                border: none;
                background: transparent;
                margin: 0px;
                padding: 0px;
            }
            QListWidget::indicator:checked,
            QListWidget::indicator:unchecked {
                width: 0px;
                height: 0px;
                border: none;
                image: none;
            }
        """)
        self._file_list.itemDoubleClicked.connect(self._on_double_click)
        self._file_list.setContextMenuPolicy(
            Qt.ContextMenuPolicy.CustomContextMenu)
        self._file_list.customContextMenuRequested.connect(
            self._show_context_menu)
        self._file_list.model().rowsMoved.connect(self._on_rows_moved)
        self._file_list.fileDroppedOnFolder.connect(self._handle_drop_on_folder)
        self._sb_list.fileDroppedOnSidebarFolder.connect(
            self._handle_drop_on_sidebar_folder)
        self._sb_list.sidebarFileToFolder.connect(
            self._handle_sidebar_file_to_folder)
        self._sb_list.addToQuickAccess.connect(
            self._handle_add_to_quick_access)
        rl.addWidget(self._file_list)

        # Bottom action bar
        btn_row = QHBoxLayout()
        btn_row.setSpacing(6)

        btn_browse = QPushButton("Browse\u2026")
        btn_browse.setStyleSheet(
            "QPushButton { padding: 7px 14px; border: 1px solid #c0c8d4;"
            " border-radius: 4px; background: white;"
            " color: #1a1a2e; font-size: 12px; }"
            " QPushButton:hover { background: #f0f4ff; }")
        btn_browse.setToolTip("Open system file browser")
        btn_browse.clicked.connect(self._browse_file)
        btn_row.addWidget(btn_browse)

        btn_new_sub = QPushButton("+ Subfolder")
        btn_new_sub.setStyleSheet(self._SM_BTN)
        btn_new_sub.setToolTip("Create a new subfolder inside the current folder")
        btn_new_sub.clicked.connect(self._create_subfolder)
        btn_row.addWidget(btn_new_sub)

        btn_add_to_folder = QPushButton("+ Add File")
        btn_add_to_folder.setStyleSheet(self._SM_BTN)
        btn_add_to_folder.setToolTip(
            "Import a .euclid file into the current folder")
        btn_add_to_folder.clicked.connect(self._add_file_to_folder)
        btn_row.addWidget(btn_add_to_folder)

        btn_delete = QPushButton("Delete")
        btn_delete.setStyleSheet(
            "QPushButton { padding: 7px 14px; border: 1px solid #e0b0b0;"
            " border-radius: 4px; background: white;"
            " color: #d32f2f; font-size: 12px; }"
            " QPushButton:hover { background: #fff0f0; }")
        btn_delete.setToolTip("Delete selected file or folder")
        btn_delete.clicked.connect(self._delete_selected)
        btn_row.addWidget(btn_delete)

        btn_row.addStretch()

        btn_cancel = QPushButton("Cancel")
        btn_cancel.setStyleSheet(
            "QPushButton { padding: 7px 20px; border: 1px solid #c0c8d4;"
            " border-radius: 4px; background: white;"
            " color: #1a1a2e; font-size: 12px; }"
            " QPushButton:hover { background: #f0f0f0; }")
        btn_cancel.clicked.connect(self.reject)
        btn_row.addWidget(btn_cancel)

        btn_open = QPushButton("Open")
        btn_open.setStyleSheet(
            "QPushButton { padding: 7px 20px; border: none;"
            " border-radius: 4px; background: #2d70b3;"
            " color: white; font-size: 12px; font-weight: 600; }"
            " QPushButton:hover { background: #1a5fa0; }")
        btn_open.clicked.connect(self._on_open)
        btn_row.addWidget(btn_open)
        rl.addLayout(btn_row)

        root.addWidget(right, stretch=1)

        # Default to unsolved proofs
        self._active_path = None
        self._load_folder(self._unsolved_dir)

        # Restore saved position and size
        geo = self._prefs.get("dialog_geometry")
        if geo:
            self.move(geo.get("x", 100), geo.get("y", 100))
            self.resize(geo.get("w", 720), geo.get("h", 520))

    # ── Persistence ────────────────────────────────────────────────────

    def _save_geometry(self):
        """Persist dialog position and size."""
        pos = self.pos()
        size = self.size()
        self._prefs["dialog_geometry"] = {
            "x": pos.x(), "y": pos.y(),
            "w": size.width(), "h": size.height(),
        }
        _save_user_bookmarks(self._prefs)

    def _custom_order_path(self, folder: str) -> str:
        """Path for the custom ordering JSON file within a folder."""
        return os.path.join(folder, ".euclid_order.json")

    def _load_custom_order(self, folder: str) -> list[str] | None:
        """Load persisted custom ordering for a folder, or None."""
        p = self._custom_order_path(folder)
        if os.path.exists(p):
            try:
                with open(p, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return None

    def _save_custom_order(self, folder: str, order: list[str]):
        """Persist the user's custom ordering of items in a folder."""
        p = self._custom_order_path(folder)
        try:
            with open(p, "w", encoding="utf-8") as f:
                json.dump(order, f, indent=2)
        except Exception:
            pass

    def done(self, result):
        self._save_geometry()
        super().done(result)

    # ── Sidebar helpers ───────────────────────────────────────────────

    _ROLE_SB_INDEX = Qt.ItemDataRole.UserRole + 10

    def _rebuild_sidebar(self):
        """Rebuild the sidebar QListWidget from self._sb_entries."""
        self._sb_list.clear()
        _emoji_font = QFont("Segoe UI Emoji", 11)
        for idx, entry in enumerate(self._sb_entries):
            text = f"{entry['icon']}  {entry['name']}"
            item = QListWidgetItem(text)
            item.setFont(_emoji_font)
            item.setData(self._ROLE_SB_INDEX, idx)
            self._sb_list.addItem(item)

    def _update_highlight(self, active_path: str):
        """Highlight the sidebar row matching active_path."""
        for i in range(self._sb_list.count()):
            item = self._sb_list.item(i)
            idx = item.data(self._ROLE_SB_INDEX)
            if idx is not None and idx < len(self._sb_entries):
                if self._sb_entries[idx]["path"] == active_path:
                    self._sb_list.setCurrentItem(item)
                    return
        self._sb_list.clearSelection()

    def _on_sidebar_click(self, index):
        """User clicked a sidebar entry — navigate to it."""
        item = self._sb_list.currentItem()
        if not item:
            return
        idx = item.data(self._ROLE_SB_INDEX)
        if idx is None or idx >= len(self._sb_entries):
            return
        entry = self._sb_entries[idx]
        path = entry["path"]
        if os.path.isfile(path):
            self._select_file_directly(path)
        else:
            self._nav_stack.clear()
            self._load_folder(path)

    def _on_sidebar_reordered(self, *_args):
        """After dragging sidebar entries, sync self._sb_entries and save."""
        new_order = []
        for i in range(self._sb_list.count()):
            item = self._sb_list.item(i)
            idx = item.data(self._ROLE_SB_INDEX)
            if idx is not None and idx < len(self._sb_entries):
                new_order.append(self._sb_entries[idx])
        self._sb_entries = new_order
        # Re-assign indices
        for i in range(self._sb_list.count()):
            self._sb_list.item(i).setData(self._ROLE_SB_INDEX, i)
        self._save_sidebar_bookmarks()

    def _save_sidebar_bookmarks(self):
        """Persist only the user (removable) bookmarks back to disk."""
        self._bookmarks = []
        for entry in self._sb_entries:
            if entry["removable"]:
                bm = {
                    "path": entry["path"],
                    "name": entry["name"],
                    "icon": entry["icon"],
                    "type": ("file" if os.path.isfile(entry["path"])
                             else "folder"),
                }
                self._bookmarks.append(bm)
        self._prefs["bookmarks"] = self._bookmarks
        _save_user_bookmarks(self._prefs)

    def _show_sidebar_context_menu(self, pos):
        """Right-click on a sidebar entry."""
        item = self._sb_list.itemAt(pos)
        if not item:
            return
        idx = item.data(self._ROLE_SB_INDEX)
        if idx is None or idx >= len(self._sb_entries):
            return
        entry = self._sb_entries[idx]

        menu = QMenu(self)
        menu.setStyleSheet(self._CTX_STYLE)

        act_rename = menu.addAction("Rename")
        act_rename.triggered.connect(
            lambda: self._rename_sidebar_entry(idx))

        act_icon = menu.addAction("Change Icon")
        act_icon.triggered.connect(
            lambda: self._change_sidebar_icon(idx))

        if entry["removable"]:
            menu.addSeparator()
            act_del = menu.addAction("Delete")
            act_del.triggered.connect(
                lambda: self._delete_sidebar_entry(idx))

        menu.exec(self._sb_list.mapToGlobal(pos))

    def _rename_sidebar_entry(self, idx: int):
        entry = self._sb_entries[idx]
        new_name, ok = self._white_input(
            "Rename", "Display name:", entry["name"])
        if not ok or not new_name.strip():
            return
        entry["name"] = new_name.strip()
        self._rebuild_sidebar()
        self._save_sidebar_bookmarks()

    def _change_sidebar_icon(self, idx: int):
        """Open a dialog with a text field and trigger the Windows emoji picker."""
        entry = self._sb_entries[idx]

        dlg = QDialog(self)
        dlg.setWindowTitle("Choose Icon")
        dlg.setFixedSize(320, 160)
        dlg.setStyleSheet(_DIALOG_BASE_STYLE)

        layout = QVBoxLayout(dlg)
        layout.setContentsMargins(16, 16, 16, 16)
        layout.setSpacing(10)

        lbl = QLabel("Type or paste an emoji below.\n"
                      "The Windows emoji picker (Win + .) will open automatically.")
        lbl.setWordWrap(True)
        lbl.setStyleSheet("color: #1a1a2e; background: transparent; font-size: 12px;")
        layout.addWidget(lbl)

        from PyQt6.QtWidgets import QLineEdit
        icon_input = QLineEdit(entry.get("icon", ""))
        icon_input.setMaxLength(10)  # emoji can be multiple code units (ZWJ sequences, flags, etc.)
        icon_input.setAlignment(Qt.AlignmentFlag.AlignCenter)
        icon_input.setStyleSheet(
            "QLineEdit { font-family: 'Segoe UI Emoji', 'Segoe UI Symbol', sans-serif;"
            " font-size: 24px; padding: 6px; border: 2px solid #2d70b3;"
            " border-radius: 6px; background: white; color: #1a1a2e; }")
        layout.addWidget(icon_input)

        btn_row = QHBoxLayout()
        btn_row.addStretch()
        ok_btn = QPushButton("OK")
        ok_btn.setStyleSheet(
            "QPushButton { background: #2d70b3; color: white;"
            " border: none; border-radius: 4px; padding: 6px 20px; font-size: 13px; }"
            " QPushButton:hover { background: #245f9a; }")
        ok_btn.clicked.connect(dlg.accept)
        cancel_btn = QPushButton("Cancel")
        cancel_btn.setStyleSheet(
            "QPushButton { background: white; color: #1a1a2e;"
            " border: 1px solid #c0c8d4; border-radius: 4px;"
            " padding: 6px 20px; font-size: 13px; }"
            " QPushButton:hover { background: #f0f4ff; }")
        cancel_btn.clicked.connect(dlg.reject)
        btn_row.addWidget(ok_btn)
        btn_row.addWidget(cancel_btn)
        layout.addLayout(btn_row)

        # Auto-open the Windows emoji picker after the dialog appears
        def _trigger_emoji_picker():
            icon_input.setFocus()
            icon_input.selectAll()  # So new emoji replaces the old one
            try:
                import subprocess
                # Simulate Win+. via PowerShell to open the emoji picker
                subprocess.Popen(
                    ['powershell', '-Command',
                     'Add-Type -AssemblyName System.Windows.Forms;'
                     '[System.Windows.Forms.SendKeys]::SendWait("^{BACKSPACE}");'
                     'Start-Sleep -Milliseconds 50;'],
                    creationflags=0x08000000,  # CREATE_NO_WINDOW
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                # Use ctypes to send Win+. which opens the emoji picker
                import ctypes
                user32 = ctypes.windll.user32
                VK_LWIN = 0x5B
                VK_OEM_PERIOD = 0xBE
                KEYEVENTF_KEYUP = 0x0002
                user32.keybd_event(VK_LWIN, 0, 0, 0)
                user32.keybd_event(VK_OEM_PERIOD, 0, 0, 0)
                user32.keybd_event(VK_OEM_PERIOD, 0, KEYEVENTF_KEYUP, 0)
                user32.keybd_event(VK_LWIN, 0, KEYEVENTF_KEYUP, 0)
            except Exception:
                pass  # Not on Windows or no ctypes — user can type manually

        QTimer.singleShot(300, _trigger_emoji_picker)

        if dlg.exec() == QDialog.DialogCode.Accepted:
            new_icon = _clean_emoji(icon_input.text().strip())
            if new_icon:
                entry["icon"] = new_icon
                self._rebuild_sidebar()
                self._save_sidebar_bookmarks()
                # Refresh folder label if this folder is currently open
                if self._active_path == entry.get("path"):
                    self._load_folder(self._active_path)

    def _delete_sidebar_entry(self, idx: int):
        """Delete a sidebar bookmark (with confirmation)."""
        if idx < 0 or idx >= len(self._sb_entries):
            return
        entry = self._sb_entries[idx]
        name = entry["name"]
        path = entry["path"]
        exists_on_disk = os.path.exists(path)
        is_folder = os.path.isdir(path)

        # First confirm: "Are you sure?"
        confirm = QMessageBox(self)
        confirm.setWindowTitle("Confirm Delete")
        confirm.setIcon(QMessageBox.Icon.Warning)
        confirm.setStyleSheet(self._white_msgbox_style())

        if exists_on_disk:
            confirm.setText(
                f'Are you sure you want to remove "{name}"?')
            confirm.setInformativeText(
                "You can remove it from the sidebar only, "
                "or permanently delete it from disk.")
            btn_remove = confirm.addButton(
                "Remove from Sidebar",
                QMessageBox.ButtonRole.YesRole)
            btn_disk = confirm.addButton(
                "Delete from Disk",
                QMessageBox.ButtonRole.DestructiveRole)
            confirm.addButton(QMessageBox.StandardButton.Cancel)
            confirm.exec()

            clicked = confirm.clickedButton()
            if clicked == btn_remove:
                pass  # just remove from sidebar below
            elif clicked == btn_disk:
                # Second confirm for destructive disk delete
                warn = QMessageBox(self)
                warn.setWindowTitle("Permanently Delete?")
                warn.setIcon(QMessageBox.Icon.Warning)
                warn.setStyleSheet(self._white_msgbox_style())
                extra = (" and all files inside it" if is_folder else "")
                warn.setText(
                    f'This will permanently delete "{name}"'
                    f'{extra}. This cannot be undone.')
                warn.setStandardButtons(
                    QMessageBox.StandardButton.Yes
                    | QMessageBox.StandardButton.No)
                warn.setDefaultButton(QMessageBox.StandardButton.No)
                if warn.exec() != QMessageBox.StandardButton.Yes:
                    return
                import shutil
                try:
                    if is_folder:
                        shutil.rmtree(path)
                    elif os.path.isfile(path):
                        os.remove(path)
                except OSError as e:
                    mb = QMessageBox(self)
                    mb.setWindowTitle("Error")
                    mb.setText(f"Could not delete:\n{e}")
                    mb.setStyleSheet(self._white_msgbox_style())
                    mb.exec()
                    return
            else:
                return  # Cancel
        else:
            # Path doesn't exist on disk — just confirm sidebar removal
            confirm.setText(
                f'Remove "{name}" from Quick Access?')
            confirm.setStandardButtons(
                QMessageBox.StandardButton.Yes
                | QMessageBox.StandardButton.No)
            confirm.setDefaultButton(QMessageBox.StandardButton.No)
            if confirm.exec() != QMessageBox.StandardButton.Yes:
                return

        # Remove from entries list
        old_path = entry["path"]
        self._sb_entries.pop(idx)
        self._rebuild_sidebar()
        self._save_sidebar_bookmarks()
        # If we were viewing this folder, go to unsolved
        if self._active_path == old_path:
            self._nav_stack.clear()
            self._load_folder(self._unsolved_dir)

    # ── Folder / file loading ─────────────────────────────────────────

    def _load_folder(self, folder: str):
        self._file_list.clear()
        self._active_path = folder
        basename = os.path.basename(folder)
        display_name = basename.replace("_", " ").title()
        # Look up icon and custom name from sidebar entries for this folder
        folder_icon = ""
        for entry in self._sb_entries:
            if entry.get("path") == folder:
                folder_icon = entry.get("icon", "")
                # Use the sidebar entry's custom display name if available
                display_name = entry.get("name", display_name)
                break
        if folder_icon:
            self._folder_label.setText(f"{folder_icon}  {display_name}")
        else:
            self._folder_label.setText(display_name)
        self._folder_label.setFont(
            QFont("Segoe UI Emoji", 12, QFont.Weight.Bold))
        self._update_highlight(folder)
        self._back_btn.setVisible(len(self._nav_stack) > 0)

        if not os.path.isdir(folder):
            item = QListWidgetItem("(folder not found)")
            item.setFlags(Qt.ItemFlag.NoItemFlags)
            self._file_list.addItem(item)
            return

        # Gather subfolders and .euclid files
        subfolders = sorted(
            (d for d in os.listdir(folder)
             if os.path.isdir(os.path.join(folder, d))
             and not d.startswith(".")),
            key=_natural_sort_key)
        files = sorted(
            (f for f in os.listdir(folder)
             if f.endswith(".euclid")
             and os.path.isfile(os.path.join(folder, f))),
            key=_natural_sort_key)

        # Apply custom order if one exists
        custom_order = self._load_custom_order(folder)
        if custom_order is not None:
            ordered_names = []
            remaining_dirs = list(subfolders)
            remaining_files = list(files)
            for name in custom_order:
                if name in remaining_dirs:
                    ordered_names.append(name)
                    remaining_dirs.remove(name)
                elif name in remaining_files:
                    ordered_names.append(name)
                    remaining_files.remove(name)
            # Append any new items not in the saved order
            for d in remaining_dirs:
                ordered_names.append(d)
            for f in remaining_files:
                ordered_names.append(f)
            all_entries = ordered_names
        else:
            all_entries = subfolders + files

        # Show a ".." parent row when inside a subfolder — can drag files onto it
        parent_dir = os.path.dirname(folder)
        if (self._nav_stack and parent_dir
                and parent_dir != folder and os.path.isdir(parent_dir)):
            parent_name = os.path.basename(parent_dir)
            item = QListWidgetItem(f"\u2190  .. ({parent_name})")
            item.setData(self._ROLE_PATH, parent_dir)
            item.setData(self._ROLE_IS_FOLDER, True)
            item.setData(self._ROLE_IS_PARENT, True)
            f = QFont("Segoe UI", 12)
            item.setFont(f)
            item.setForeground(QColor("#8b8ba0"))
            # Not draggable itself, but accepts drops
            item.setFlags(Qt.ItemFlag.ItemIsEnabled
                          | Qt.ItemFlag.ItemIsDropEnabled)
            self._file_list.addItem(item)

        if not all_entries:
            item = QListWidgetItem("(empty folder)")
            item.setFlags(Qt.ItemFlag.NoItemFlags)
            self._file_list.addItem(item)
            return

        _drag_flags = (Qt.ItemFlag.ItemIsSelectable
                       | Qt.ItemFlag.ItemIsEnabled
                       | Qt.ItemFlag.ItemIsDragEnabled
                       | Qt.ItemFlag.ItemIsDropEnabled)
        for entry_name in all_entries:
            full = os.path.join(folder, entry_name)
            if os.path.isdir(full):
                display = f"\u25B8  {entry_name}"
                item = QListWidgetItem(display)
                item.setFlags(_drag_flags)
                item.setData(self._ROLE_PATH, full)
                item.setData(self._ROLE_IS_FOLDER, True)
                f = QFont("Segoe UI", 13, QFont.Weight.DemiBold)
                item.setFont(f)
                item.setForeground(QColor("#2d70b3"))
                self._file_list.addItem(item)
            elif entry_name.endswith(".euclid"):
                display = entry_name.replace(".euclid", "")
                item = QListWidgetItem(display)
                item.setFlags(_drag_flags)
                item.setData(self._ROLE_PATH, full)
                item.setData(self._ROLE_IS_FOLDER, False)
                self._file_list.addItem(item)

    def _navigate_into(self, folder: str):
        """Navigate into a subfolder, pushing current to back stack."""
        if self._active_path:
            self._nav_stack.append(self._active_path)
        self._load_folder(folder)

    def _go_back(self):
        """Navigate back to the previous folder."""
        if self._nav_stack:
            prev = self._nav_stack.pop()
            self._load_folder(prev)

    def _select_file_directly(self, path: str):
        """Sidebar file entry clicked — open it immediately."""
        if os.path.isfile(path):
            self.selected_path = path
            self.accept()

    _ROLE_IS_PARENT = Qt.ItemDataRole.UserRole + 2

    def _on_double_click(self, item: QListWidgetItem):
        path = item.data(self._ROLE_PATH)
        is_folder = item.data(self._ROLE_IS_FOLDER)
        if not path:
            return
        if item.data(self._ROLE_IS_PARENT):
            # ".." row — go back instead of navigating deeper
            self._go_back()
        elif is_folder:
            self._navigate_into(path)
        else:
            self.selected_path = path
            self.accept()

    def _on_open(self):
        item = self._file_list.currentItem()
        if item:
            path = item.data(self._ROLE_PATH)
            is_folder = item.data(self._ROLE_IS_FOLDER)
            if path:
                if is_folder:
                    self._navigate_into(path)
                else:
                    self.selected_path = path
                    self.accept()

    def _browse_file(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Open Euclid File", "",
            "Euclid Files (*.euclid);;All Files (*)")
        if path:
            self.selected_path = path
            self.accept()

    # ── Drag & drop reorder persistence ────────────────────────────────

    def _on_rows_moved(self, *_args):
        """After the user reorders items via drag-drop, persist the order."""
        if not self._active_path or not os.path.isdir(self._active_path):
            return
        order = []
        for i in range(self._file_list.count()):
            item = self._file_list.item(i)
            path = item.data(self._ROLE_PATH)
            if path:
                order.append(os.path.basename(path))
        self._save_custom_order(self._active_path, order)

    # ── Context menu (right-click) ─────────────────────────────────────

    _CTX_STYLE = (
        "QMenu { background: white; color: #1a1a2e;"
        " border: 1px solid #d0d4da; border-radius: 4px; padding: 4px; }"
        " QMenu::item { padding: 6px 20px; color: #1a1a2e; }"
        " QMenu::item:selected { background: #edf2ff; color: #1a1a2e; }"
        " QMenu::item:disabled { color: #aaa; }"
        " QMenu::separator { height: 1px; background: #e5e7eb;"
        "   margin: 4px 8px; }"
    )

    def _show_context_menu(self, pos):
        item = self._file_list.itemAt(pos)
        if not item:
            # Right-click on empty area
            menu = QMenu(self)
            menu.setStyleSheet(self._CTX_STYLE)
            act_new_folder = menu.addAction("New Folder")
            act_new_folder.triggered.connect(self._create_sidebar_folder)
            menu.exec(self._file_list.mapToGlobal(pos))
            return

        path = item.data(self._ROLE_PATH)
        is_folder = item.data(self._ROLE_IS_FOLDER)
        if not path:
            return

        menu = QMenu(self)
        menu.setStyleSheet(self._CTX_STYLE)

        if is_folder:
            act_open = menu.addAction("Open Folder")
            act_open.triggered.connect(
                lambda: self._navigate_into(path))
            menu.addSeparator()

        # Move to folder submenu
        if not is_folder and self._active_path:
            move_menu = menu.addMenu("Move to\u2026")
            move_menu.setStyleSheet(self._CTX_STYLE)

            # "Move to Parent Folder" — when inside a subfolder
            parent_dir = os.path.dirname(self._active_path)
            if (parent_dir and parent_dir != self._active_path
                    and os.path.isdir(parent_dir)):
                act_parent = move_menu.addAction(
                    f"\u2190  Parent ({os.path.basename(parent_dir)})")
                act_parent.triggered.connect(
                    lambda checked, t=parent_dir, p=path:
                        self._move_to_folder(p, t))
                move_menu.addSeparator()

            # Sibling subfolders within current folder
            try:
                subdirs = sorted(
                    d for d in os.listdir(self._active_path)
                    if os.path.isdir(os.path.join(self._active_path, d))
                    and not d.startswith("."))
                for sd in subdirs:
                    target = os.path.join(self._active_path, sd)
                    act = move_menu.addAction(f"\u25B8  {sd}")
                    act.triggered.connect(
                        lambda checked, t=target, p=path:
                            self._move_to_folder(p, t))
            except OSError:
                pass

            # Sidebar folders (Quick Access)
            sb_folders = [
                e for e in self._sb_entries
                if os.path.isdir(e.get("path", ""))
                and e["path"] != self._active_path
                and e["path"] != parent_dir
            ]
            if sb_folders:
                move_menu.addSeparator()
                for entry in sb_folders:
                    icon = entry.get("icon", "\u25B8")
                    act = move_menu.addAction(
                        f"{icon}  {entry['name']}")
                    act.triggered.connect(
                        lambda checked, t=entry["path"], p=path:
                            self._move_to_folder(p, t))

            if not move_menu.actions():
                move_menu.addAction("(no folders available)").setEnabled(False)
            menu.addSeparator()

        act_rename = menu.addAction("Rename")
        act_rename.triggered.connect(
            lambda: self._rename_item(item))
        menu.addSeparator()

        act_del = menu.addAction("Delete")
        act_del.triggered.connect(
            lambda: self._delete_item(path, is_folder))

        menu.exec(self._file_list.mapToGlobal(pos))

    # ── Folder creation ────────────────────────────────────────────────

    @staticmethod
    def _white_msgbox_style():
        return ("QMessageBox { background: white; }"
                " QLabel { color: #1a1a2e; background: transparent; }"
                " QPushButton { background: white; color: #1a1a2e;"
                "   border: 1px solid #c0c8d4; border-radius: 4px;"
                "   padding: 5px 16px; }"
                " QPushButton:hover { background: #f0f4ff; }")

    def _white_input(self, title, label, text=""):
        """Show a white-themed QInputDialog and return (text, ok)."""
        from PyQt6.QtWidgets import QInputDialog
        dlg = QInputDialog(self)
        dlg.setWindowTitle(title)
        dlg.setLabelText(label)
        dlg.setTextValue(text)
        dlg.setStyleSheet(
            "QInputDialog { background: white; }"
            " QLabel { color: #1a1a2e; background: transparent; }"
            " QLineEdit { background: white; color: #1a1a2e;"
            "   border: 1px solid #c0c8d4; border-radius: 4px;"
            "   padding: 4px 8px; }"
            " QPushButton { background: white; color: #1a1a2e;"
            "   border: 1px solid #c0c8d4; border-radius: 4px;"
            "   padding: 5px 16px; }"
            " QPushButton:hover { background: #f0f4ff; }")
        ok = dlg.exec() == QInputDialog.DialogCode.Accepted
        return dlg.textValue(), ok

    def _create_sidebar_folder(self):
        """Create a brand-new folder and add it to the Quick Access sidebar."""
        name, ok = self._white_input(
            "New Folder", "Folder name:", "New Folder")
        if not ok or not name.strip():
            return
        name = name.strip()

        # Create the folder next to the app's data directories
        from ..resources import resource_path
        base = resource_path("")
        target = os.path.join(base, name)

        if os.path.exists(target):
            # If it already exists, check if already in sidebar
            for entry in self._sb_entries:
                if entry["path"] == target:
                    self._nav_stack.clear()
                    self._load_folder(target)
                    return
        else:
            try:
                os.makedirs(target)
            except OSError as e:
                mb = QMessageBox(self)
                mb.setWindowTitle("Error")
                mb.setText(f"Could not create folder:\n{e}")
                mb.setStyleSheet(self._white_msgbox_style())
                mb.exec()
                return

        # Add to sidebar entries
        self._sb_entries.append({
            "path": target,
            "name": name,
            "icon": "\u25B8",
            "removable": True,
        })
        self._rebuild_sidebar()
        self._save_sidebar_bookmarks()
        self._nav_stack.clear()
        self._load_folder(target)

    def _create_subfolder(self):
        """Create a new subfolder inside the currently viewed folder."""
        if not self._active_path or not os.path.isdir(self._active_path):
            return
        name, ok = self._white_input(
            "New Subfolder", "Subfolder name:", "New Folder")
        if not ok or not name.strip():
            return
        name = name.strip()
        target = os.path.join(self._active_path, name)
        if os.path.exists(target):
            mb = QMessageBox(self)
            mb.setWindowTitle("Folder Exists")
            mb.setText(f'A folder named "{name}" already exists here.')
            mb.setStyleSheet(self._white_msgbox_style())
            mb.exec()
            return
        try:
            os.makedirs(target)
        except OSError as e:
            mb = QMessageBox(self)
            mb.setWindowTitle("Error")
            mb.setText(f"Could not create folder:\n{e}")
            mb.setStyleSheet(self._white_msgbox_style())
            mb.exec()
            return
        self._load_folder(self._active_path)

    def _add_file_to_folder(self):
        """Import a .euclid file (copy) into the currently viewed folder."""
        if not self._active_path or not os.path.isdir(self._active_path):
            return
        paths, _ = QFileDialog.getOpenFileNames(
            self, "Add File to Folder", "",
            "Euclid Files (*.euclid);;All Files (*)")
        if not paths:
            return
        import shutil
        for src in paths:
            fname = os.path.basename(src)
            dest = os.path.join(self._active_path, fname)
            if os.path.abspath(src) == os.path.abspath(dest):
                continue  # already in this folder
            if os.path.exists(dest):
                reply = QMessageBox(self)
                reply.setWindowTitle("File Exists")
                reply.setText(
                    f'"{fname}" already exists here.\nOverwrite it?')
                reply.setStandardButtons(
                    QMessageBox.StandardButton.Yes
                    | QMessageBox.StandardButton.No)
                reply.setDefaultButton(QMessageBox.StandardButton.No)
                reply.setStyleSheet(self._white_msgbox_style())
                if reply.exec() != QMessageBox.StandardButton.Yes:
                    continue
            try:
                shutil.copy2(src, dest)
            except OSError:
                pass
        self._load_folder(self._active_path)

    # ── Move file to folder ────────────────────────────────────────────

    def _move_to_folder(self, file_path: str, folder_path: str):
        """Move a .euclid file into a subfolder."""
        import shutil
        fname = os.path.basename(file_path)
        dest = os.path.join(folder_path, fname)
        if os.path.exists(dest):
            reply = QMessageBox(self)
            reply.setWindowTitle("File Exists")
            reply.setText(
                f'"{fname}" already exists in '
                f'"{os.path.basename(folder_path)}".\nOverwrite it?')
            reply.setStandardButtons(
                QMessageBox.StandardButton.Yes
                | QMessageBox.StandardButton.No)
            reply.setDefaultButton(QMessageBox.StandardButton.No)
            reply.setStyleSheet(self._white_msgbox_style())
            if reply.exec() != QMessageBox.StandardButton.Yes:
                return
        try:
            shutil.move(file_path, dest)
        except OSError as e:
            mb = QMessageBox(self)
            mb.setWindowTitle("Error")
            mb.setText(f"Could not move file:\n{e}")
            mb.setStyleSheet(self._white_msgbox_style())
            mb.exec()
            return
        self._load_folder(self._active_path)

    # ── Drag-and-drop into folders ────────────────────────────────────

    def _handle_drop_on_folder(self, source_path: str, target_folder: str):
        """Handle a file dropped onto a folder in the file list."""
        if source_path.startswith("__sb__"):
            # Dropped from sidebar — resolve path from sidebar entry
            try:
                sb_idx = int(source_path.replace("__sb__", ""))
                if 0 <= sb_idx < len(self._sb_entries):
                    source_path = self._sb_entries[sb_idx]["path"]
                else:
                    return
            except (ValueError, IndexError):
                return
        if not source_path or not os.path.isfile(source_path):
            return
        if os.path.isdir(target_folder):
            self._move_to_folder(source_path, target_folder)

    def _handle_drop_on_sidebar_folder(self, source_path: str,
                                        target_ref: str):
        """Handle a file dropped onto a sidebar folder entry."""
        if target_ref.startswith("__sb__"):
            try:
                sb_idx = int(target_ref.replace("__sb__", ""))
                if 0 <= sb_idx < len(self._sb_entries):
                    target_folder = self._sb_entries[sb_idx]["path"]
                else:
                    return
            except (ValueError, IndexError):
                return
        else:
            target_folder = target_ref

        if not source_path or not os.path.isfile(source_path):
            # File might not exist if Qt's InternalMove already removed it
            # from the list — reload to restore
            QTimer.singleShot(0, lambda: self._load_folder(self._active_path))
            return
        if not os.path.isdir(target_folder):
            return
        # Don't move into the same folder
        if os.path.dirname(source_path) == target_folder:
            QTimer.singleShot(0, lambda: self._load_folder(self._active_path))
            return
        self._move_to_folder(source_path, target_folder)

    def _sb_idx_is_folder(self, idx: int) -> bool:
        """Check if a sidebar entry at idx is a folder on disk."""
        if 0 <= idx < len(self._sb_entries):
            return os.path.isdir(self._sb_entries[idx].get("path", ""))
        return False

    def _handle_sidebar_file_to_folder(self, src_idx: int, tgt_idx: int):
        """Handle a sidebar file entry dropped onto a sidebar folder entry."""
        if src_idx < 0 or src_idx >= len(self._sb_entries):
            return
        if tgt_idx < 0 or tgt_idx >= len(self._sb_entries):
            return
        src_entry = self._sb_entries[src_idx]
        tgt_entry = self._sb_entries[tgt_idx]
        src_path = src_entry.get("path", "")
        tgt_folder = tgt_entry.get("path", "")

        if not src_path or not os.path.isfile(src_path):
            return
        if not tgt_folder or not os.path.isdir(tgt_folder):
            return
        # Don't move into same folder
        if os.path.dirname(src_path) == tgt_folder:
            return

        self._move_to_folder(src_path, tgt_folder)

        # Remove the file entry from the sidebar since it's been moved
        if src_entry.get("removable"):
            # Recalculate index since _move_to_folder may have refreshed
            try:
                idx = self._sb_entries.index(src_entry)
                self._sb_entries.pop(idx)
                self._rebuild_sidebar()
                self._save_sidebar_bookmarks()
            except ValueError:
                pass

    def _handle_add_to_quick_access(self, file_path: str):
        """Move a file out of its current folder and add as a Quick Access
        bookmark.  The file is moved to the project root so it is no longer
        inside the source folder."""
        if not file_path:
            return

        # Move the file to the project root so it leaves the folder
        import shutil
        if os.path.isfile(file_path):
            from ..resources import resource_path
            root = resource_path("")
            parent_dir = os.path.dirname(file_path)
            if parent_dir != root:
                dest = os.path.join(root, os.path.basename(file_path))
                if os.path.exists(dest):
                    # Dest already exists — remove the source (it's a dup)
                    os.remove(file_path)
                else:
                    shutil.move(file_path, dest)
                file_path = dest

        # Don't add duplicates
        for entry in self._sb_entries:
            if entry["path"] == file_path:
                return
        is_dir = os.path.isdir(file_path)
        name = os.path.basename(file_path)
        if not is_dir:
            name = name.replace(".euclid", "")
        self._sb_entries.append({
            "path": file_path,
            "name": name,
            "icon": "\u25B8" if is_dir else "\u2022",
            "removable": True,
        })
        self._rebuild_sidebar()
        self._save_sidebar_bookmarks()
        # Force-reload the file list so the moved file disappears.
        # Use a short delay so Qt finishes its internal drag bookkeeping
        # before we rebuild the list.
        active = self._active_path
        QTimer.singleShot(50, lambda: self._load_folder(active))

    # ── Rename ─────────────────────────────────────────────────────────

    def _rename_item(self, item: QListWidgetItem):
        path = item.data(self._ROLE_PATH)
        if not path:
            return
        old_name = os.path.basename(path)
        is_folder = item.data(self._ROLE_IS_FOLDER)
        prompt_name = (old_name if is_folder
                       else old_name.replace(".euclid", ""))
        new_name, ok = self._white_input(
            "Rename", "New name:", prompt_name)
        if not ok or not new_name.strip():
            return
        new_name = new_name.strip()
        if not is_folder and not new_name.endswith(".euclid"):
            new_name += ".euclid"
        new_path = os.path.join(os.path.dirname(path), new_name)
        if os.path.exists(new_path) and new_path != path:
            mb = QMessageBox(self)
            mb.setWindowTitle("Name Taken")
            mb.setText(f'"{new_name}" already exists.')
            mb.setStyleSheet(self._white_msgbox_style())
            mb.exec()
            return
        try:
            os.rename(path, new_path)
        except OSError as e:
            mb = QMessageBox(self)
            mb.setWindowTitle("Error")
            mb.setText(f"Could not rename:\n{e}")
            mb.setStyleSheet(self._white_msgbox_style())
            mb.exec()
            return
        self._load_folder(self._active_path)

    # ── Delete with confirmation ───────────────────────────────────────

    def _delete_selected(self):
        """Delete button in the toolbar — delete all selected items."""
        items = self._file_list.selectedItems()
        if not items:
            return
        paths = []
        for it in items:
            p = it.data(self._ROLE_PATH)
            if p:
                paths.append((p, it.data(self._ROLE_IS_FOLDER)))
        if not paths:
            return
        n = len(paths)
        if n == 1:
            name = os.path.basename(paths[0][0])
            msg = f'Are you sure you want to delete "{name}"?'
        else:
            msg = f"Are you sure you want to delete {n} items?"

        confirm = QMessageBox(self)
        confirm.setWindowTitle("Confirm Delete")
        confirm.setText(msg)
        confirm.setInformativeText("This action cannot be undone.")
        confirm.setIcon(QMessageBox.Icon.Warning)
        confirm.setStandardButtons(
            QMessageBox.StandardButton.Yes
            | QMessageBox.StandardButton.No)
        confirm.setDefaultButton(QMessageBox.StandardButton.No)
        confirm.setStyleSheet(self._white_msgbox_style())
        if confirm.exec() != QMessageBox.StandardButton.Yes:
            return

        import shutil
        for p, is_dir in paths:
            try:
                if is_dir:
                    shutil.rmtree(p)
                else:
                    os.remove(p)
            except OSError:
                pass
        self._load_folder(self._active_path)

    def _delete_item(self, path: str, is_folder: bool):
        """Delete a single item (from context menu)."""
        name = os.path.basename(path)
        kind = "folder" if is_folder else "file"
        extra = ("\nAll files inside the folder will also be deleted."
                 if is_folder else "")
        confirm = QMessageBox(self)
        confirm.setWindowTitle("Confirm Delete")
        confirm.setText(
            f'Are you sure you want to delete the {kind} '
            f'"{name}"?{extra}')
        confirm.setInformativeText("This action cannot be undone.")
        confirm.setIcon(QMessageBox.Icon.Warning)
        confirm.setStandardButtons(
            QMessageBox.StandardButton.Yes
            | QMessageBox.StandardButton.No)
        confirm.setDefaultButton(QMessageBox.StandardButton.No)
        confirm.setStyleSheet(self._white_msgbox_style())
        if confirm.exec() != QMessageBox.StandardButton.Yes:
            return

        import shutil
        try:
            if is_folder:
                shutil.rmtree(path)
            else:
                os.remove(path)
        except OSError as e:
            mb = QMessageBox(self)
            mb.setWindowTitle("Error")
            mb.setText(f"Could not delete:\n{e}")
            mb.setStyleSheet(self._white_msgbox_style())
            mb.exec()
            return
        self._load_folder(self._active_path)

    # ── Bookmark management ───────────────────────────────────────────

    def _add_file_bookmark(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Add File to Sidebar", "",
            "Euclid Files (*.euclid);;All Files (*)")
        if not path:
            return
        for entry in self._sb_entries:
            if entry["path"] == path:
                return
        name = os.path.basename(path).replace(".euclid", "")
        self._sb_entries.append({
            "path": path,
            "name": name,
            "icon": "\u2022",
            "removable": True,
        })
        self._rebuild_sidebar()
        self._save_sidebar_bookmarks()


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

        # Auto-load a blank proof so the canvas is ready immediately
        QTimer.singleShot(0, self.open_blank)

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
