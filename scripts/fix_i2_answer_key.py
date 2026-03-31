"""Fix I.2 answer key: replace generic justifications and add construction refs."""
path = "answer_key_book_1.json"
with open(path, "r", encoding="utf-8") as f:
    c = f.read()

i2_start = c.index('"Prop.I.2"')
i2_end = c.index('"Prop.I.3"', i2_start)
section = c[i2_start:i2_end]

fixes = [
    ('"justification": "Diagrammatic"', '"justification": "Betweenness 1c"'),
    ('"justification": "Metric"', '"justification": "CN1"'),
    ('"justification": "Diagrammatic"', '"justification": "Circle 2c"'),
    ('"justification": "Transfer"', '"justification": "Segment transfer 6"'),
    ('"justification": "Metric"', '"justification": "CN1"'),
    ('"justification": "Transfer"', '"justification": "Segment transfer 5"'),
    ('"justification": "Transfer"', '"justification": "Segment transfer 1"'),
    ('"justification": "Transfer"', '"justification": "Segment transfer 1"'),
    ('"justification": "Metric"', '"justification": "CN3"'),
    ('"justification": "Metric"', '"justification": "CN1"'),
]

for old, new in fixes:
    if old in section:
        section = section.replace(old, new, 1)
        print(f"Applied: {old} -> {new}")

old_10 = '"refs": [\n              9,\n              7\n            ]'
new_10 = '"refs": [\n              9,\n              7,\n              6\n            ]'
if old_10 in section:
    section = section.replace(old_10, new_10, 1)
    print("Line 10: added ref 6")

old_20 = '"refs": [\n              19,\n              14\n            ]'
new_20 = '"refs": [\n              19,\n              14,\n              6\n            ]'
if old_20 in section:
    section = section.replace(old_20, new_20, 1)
    print("Line 20: added ref 6")

c = c[:i2_start] + section + c[i2_end:]
with open(path, "w", encoding="utf-8") as f:
    f.write(c)
print("Done.")
