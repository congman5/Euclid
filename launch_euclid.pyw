"""Launch the Euclid Simulator GUI (windowless — no console)."""
import os
import sys

# Ensure the project root is on sys.path so 'euclid_py' is importable
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from euclid_py.__main__ import main

main()
