"""
fitch_theme.py — Shared palette, fonts, spacing, and stylesheet constants
for the Fitch-style proof UI.

Design direction: minimal, crisp, academic, modern, readable.
Inspired by the Fitch proof tool with dark teal scope bars,
generous line spacing, and restrained colour use.
"""
from __future__ import annotations

from PyQt6.QtGui import QColor, QFont


# ═══════════════════════════════════════════════════════════════════════════
# COLOUR PALETTE
# ═══════════════════════════════════════════════════════════════════════════

class C:
    """Colour constants — kept as hex strings for stylesheets."""
    # Backgrounds
    bg = "#f8f8f8"
    surface = "#ffffff"
    surface_hover = "#f0f4ff"
    surface_selected = "#e0ebff"

    # Scope bars & structure
    scope_bar = "#2e6e6e"       # Dark teal (matches Fitch screenshots)
    scope_bar_light = "#5a9e9e"
    assumption_bg = "#fdfaf5"   # Very faint warm tint for assumption lines

    # Text
    text = "#1a1a2e"
    text_secondary = "#5a5a72"
    text_muted = "#8b8ba0"
    text_formula = "#1a1a2e"    # Main formula text — must be dominant
    text_just = "#3a6e3a"       # Justification text — muted green (matches Fitch)

    # Status
    valid = "#2e8b57"           # Checkmark green
    invalid = "#cc3333"         # Error red
    pending = "#8b8ba0"         # Neutral grey for ?

    # Error highlighting
    error_bg = "#fff0f0"
    error_bg_deep = "#ffe0e0"
    error_border = "#cc3333"

    # Borders & dividers
    border = "#e0e0e8"
    border_light = "#ececf0"

    # Accent
    primary = "#2d70b3"
    primary_light = "#e0ebff"

    # Header
    header_bg = "#1e3a5f"       # Deep navy — contrasts with logo's bright blue
    header_text = "#ffffff"

    # Goal panel
    goal_bg = "#f5f5fa"
    goal_border = "#d0d0e0"


# ═══════════════════════════════════════════════════════════════════════════
# FONTS
# ═══════════════════════════════════════════════════════════════════════════

class Fonts:
    """Font constants — academic, mathematical feel."""

    @staticmethod
    def formula(size: int = 14) -> QFont:
        f = QFont("Cambria Math", size)
        f.setStyleHint(QFont.StyleHint.Serif)
        return f

    @staticmethod
    def formula_mono(size: int = 13) -> QFont:
        """Monospace formula font for alignment."""
        f = QFont("Consolas", size)
        f.setStyleHint(QFont.StyleHint.Monospace)
        return f

    @staticmethod
    def ui(size: int = 12) -> QFont:
        f = QFont("Segoe UI", size)
        f.setStyleHint(QFont.StyleHint.SansSerif)
        return f

    @staticmethod
    def ui_bold(size: int = 12) -> QFont:
        f = QFont("Segoe UI", size, QFont.Weight.Bold)
        f.setStyleHint(QFont.StyleHint.SansSerif)
        return f

    @staticmethod
    def heading(size: int = 11) -> QFont:
        f = QFont("Segoe UI", size, QFont.Weight.DemiBold)
        f.setStyleHint(QFont.StyleHint.SansSerif)
        f.setLetterSpacing(QFont.SpacingType.AbsoluteSpacing, 1.2)
        return f

    @staticmethod
    def line_number(size: int = 11) -> QFont:
        f = QFont("Consolas", size)
        f.setStyleHint(QFont.StyleHint.Monospace)
        return f


# ═══════════════════════════════════════════════════════════════════════════
# SPACING
# ═══════════════════════════════════════════════════════════════════════════

class Sp:
    """Spacing constants in pixels."""
    line_height = 36          # Height of a single proof line row
    scope_bar_width = 3       # Width of vertical scope bars
    scope_indent = 20         # Horizontal indent per depth level
    line_number_width = 40    # Width of the line number column
    status_width = 24         # Width of the status icon column
    just_min_width = 180      # Minimum width for justification column
    padding = 12              # General padding
    padding_sm = 6
    padding_lg = 20


# ═══════════════════════════════════════════════════════════════════════════
# STYLESHEET FRAGMENTS
# ═══════════════════════════════════════════════════════════════════════════

MAIN_STYLESHEET = f"""
QMainWindow {{
    background: {C.bg};
}}

QWidget#proof_view {{
    background: {C.surface};
    border: 1px solid {C.border};
}}

QLabel {{
    color: {C.text};
}}

QLabel#section_header {{
    color: {C.text_secondary};
    font-size: 11px;
    font-weight: 600;
    letter-spacing: 1.2px;
    text-transform: uppercase;
    padding: 8px 12px 4px 12px;
}}

QPushButton {{
    background: {C.surface};
    color: {C.text};
    border: 1px solid {C.border};
    border-radius: 4px;
    padding: 6px 14px;
    font-size: 13px;
}}
QPushButton:hover {{
    background: {C.surface_hover};
    border-color: {C.primary};
}}
QPushButton:pressed {{
    background: {C.primary_light};
}}
QPushButton#primary_btn {{
    background: {C.primary};
    color: white;
    border-color: {C.primary};
}}
QPushButton#primary_btn:hover {{
    background: #245f9a;
}}

QToolBar {{
    background: {C.surface};
    border-bottom: 1px solid {C.border};
    spacing: 4px;
    padding: 4px;
}}

QStatusBar {{
    background: {C.surface};
    border-top: 1px solid {C.border};
    color: {C.text_secondary};
    font-size: 12px;
}}

QScrollArea {{
    border: none;
    background: transparent;
}}

QSplitter::handle {{
    background: {C.border};
    width: 1px;
}}

QLineEdit {{
    background: {C.surface};
    color: {C.text};
    border: 1px solid {C.border};
    border-radius: 4px;
    padding: 6px 10px;
    font-size: 13px;
}}
QLineEdit:focus {{
    border-color: {C.primary};
}}

QListWidget {{
    background: {C.surface};
    color: {C.text};
    border: none;
}}
QListWidget::item {{
    color: {C.text};
    padding: 10px 16px;
    border-bottom: 1px solid {C.border_light};
}}
QListWidget::item:hover {{
    background: {C.surface_hover};
}}
QListWidget::item:selected {{
    background: {C.surface_selected};
}}

QComboBox {{
    background: {C.surface};
    color: {C.text};
    border: 1px solid {C.border};
    border-radius: 4px;
    padding: 4px 8px;
    font-size: 13px;
}}
QComboBox:focus {{
    border-color: {C.primary};
}}
QComboBox QAbstractItemView {{
    background: {C.surface};
    color: {C.text};
    selection-background-color: {C.surface_selected};
}}

QGraphicsView {{
    background: {C.surface};
    border: 1px solid {C.border};
}}

QScrollBar:horizontal {{
    background: {C.bg};
    height: 10px;
    border: none;
    margin: 0;
}}
QScrollBar::handle:horizontal {{
    background: {C.border};
    border-radius: 4px;
    min-width: 30px;
}}
QScrollBar::handle:horizontal:hover {{
    background: {C.text_muted};
}}
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {{
    width: 0;
}}

QScrollBar:vertical {{
    background: {C.bg};
    width: 10px;
    border: none;
    margin: 0;
}}
QScrollBar::handle:vertical {{
    background: {C.border};
    border-radius: 4px;
    min-height: 30px;
}}
QScrollBar::handle:vertical:hover {{
    background: {C.text_muted};
}}
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{
    height: 0;
}}

QToolButton {{
    background: {C.surface};
    color: {C.text};
    border: 1px solid {C.border};
    border-radius: 4px;
    padding: 4px 10px;
    font-size: 15px;
    min-width: 28px;
    min-height: 28px;
}}
QToolButton:hover {{
    background: {C.surface_hover};
    border-color: {C.primary};
}}
QToolButton:checked {{
    background: {C.primary_light};
    border-color: {C.primary};
    color: {C.primary};
}}

QSplitter::handle:horizontal {{
    background: {C.border};
    width: 3px;
    margin: 0 1px;
}}
QSplitter::handle:horizontal:hover {{
    background: {C.primary};
}}
"""


# ═══════════════════════════════════════════════════════════════════════════
# UNICODE SYMBOLS
# ═══════════════════════════════════════════════════════════════════════════

class Sym:
    """Unicode symbols for proof display."""
    check = "✓"
    cross = "✗"
    pending = "?"
    assumption = "▼"      # Assumption indicator (as in Fitch)
    turnstile = "⊢"
    bottom = "⊥"
    forall = "∀"
    exists = "∃"
    neg = "¬"
    conj = "∧"
    disj = "∨"
    impl = "→"
    iff = "↔"
    neq = "≠"

    # Greek letters — commonly used in geometric proofs
    alpha = "α"
    beta = "β"
    gamma = "γ"
    delta = "δ"
    epsilon = "ε"
    zeta = "ζ"
    eta = "η"
    theta = "θ"
    iota = "ι"
    kappa = "κ"
    lambda_ = "λ"
    mu = "μ"
    nu = "ν"
    xi = "ξ"
    rho = "ρ"
    sigma = "σ"
    tau = "τ"
    phi = "φ"
    chi = "χ"
    psi = "ψ"
    omega = "ω"
