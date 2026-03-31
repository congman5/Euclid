import json, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
data = json.load(open("verified_proofs_book_1.json", "r", encoding="utf-8"))
# Find the I.9 proof
if isinstance(data, dict):
    p9 = data.get("Prop.I.9", data)
elif isinstance(data, list):
    for item in data:
        if isinstance(item, dict) and item.get("name") == "Prop.I.9":
            p9 = item
            break
    else:
        # Maybe it's keyed differently
        print("Type:", type(data))
        if isinstance(data, list) and len(data) > 0:
            print("First item type:", type(data[0]))
            if isinstance(data[0], str):
                print("First:", data[0][:100])
        sys.exit(1)

print("Name:", p9.get("name"))
print("Premises:", p9.get("premises"))
print("Goal:", p9.get("goal"))
print()
for line in p9.get("lines", []):
    lid = line.get("id", "?")
    stmt = line.get("statement", "?")
    just = line.get("justification", "?")
    deps = line.get("refs", [])
    depth = line.get("depth", 0)
    indent = "  " * depth
    print(f"  {indent}L{lid}: [{just}] {stmt}  deps={deps}")
