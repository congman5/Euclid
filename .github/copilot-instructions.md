# Copilot Instructions

## General Guidelines
- After every feature implemented, please add it into the changelog file change-log.md. If one does not exist, create one.
- When auditing features against the changelog, use the changelog as the source of truth for functionality. Screenshots should only be used as aesthetic/visual reference, not as functional requirements. Do not add features shown in screenshots that were explicitly removed or replaced in the changelog.

## UI Component Guidelines
- In PyQt6, for QPushButton badges with small fixed sizes (e.g. 24x20), set `padding:0px` in their stylesheet to prevent Qt's default padding from pushing the text outside the visible area, which can make buttons appear blank. Use compact inline stylesheets matching the proof panel pattern.

## Proof Journal Guidelines
- The proof journal (premises, steps, goal) and the canvas are independent. Premises like `on(a, L)` are formal assumptions evaluated by the verifier without any canvas drawing. Proofs verify correctly with an empty canvas.

