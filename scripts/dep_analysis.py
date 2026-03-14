"""Determine which failing proofs are root causes vs cascade failures."""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

d = json.load(open('answer_key_book_1.json', 'r', encoding='utf-8'))

failing = {"Prop.I.6", "Prop.I.7", "Prop.I.9", "Prop.I.10", 
           "Prop.I.11", "Prop.I.13", "Prop.I.15", "Prop.I.16"}

for name in sorted(failing):
    deps = d['propositions'][name].get('dependencies', [])
    dep_names = [f"Prop.I.{d2}" for d2 in deps]
    failing_deps = [d2 for d2 in dep_names if d2 in failing]
    if failing_deps:
        print(f"{name} depends on FAILING: {failing_deps}")
    else:
        print(f"{name} is a ROOT failure (deps: {deps})")
