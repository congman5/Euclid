"""Extract full text proofs for failing propositions."""
import sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

content = open('answer-key-book-I.txt', 'r', encoding='utf-8').readlines()
content = [l.rstrip('\n') for l in content]

for prop in ["I.6", "I.7", "I.9", "I.10", "I.11", "I.13", "I.15", "I.16"]:
    pattern = f"PROPOSITION {prop} "
    start = None
    for i, line in enumerate(content):
        if pattern in line:
            start = i
            break
    if start is None:
        print(f"NOT FOUND: {prop}")
        continue
    # Find the next proposition header (line of ===)
    end = start + 1
    for i in range(start + 2, min(start + 100, len(content))):
        if content[i].startswith("=" * 10) and i > start + 1:
            end = i - 1  # back up to before the === line
            break
    else:
        end = min(start + 80, len(content))

    print(f"\n{'='*60}")
    for line in content[start:end]:
        print(line)
    print(f"{'='*60}")
