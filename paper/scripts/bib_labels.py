#!/usr/bin/env python3
"""Write the citation label of every entry of bibliography.bib into its `abstract` field.

The paper cites with the style ieee-alpha.csl, whose labels are
  - one author:        the first three letters of the last name, then the year   [Joh62]
  - several authors:   the initials of all the last names, then the year         [BCHKS25]
  - an organization:   the first three letters of its name, then the year        [Eth25]
with a, b, ... appended when two entries get the same label. Typst's bibliography engine
(hayagriva) computes its own labels ([Ben+25] for four or more authors) and does not read
`label` or `shorthand`; the only free field that it passes on to the style is `abstract`,
so the label goes there. Run this script after adding or editing an entry:

    python3 paper/scripts/bib_labels.py            # update bibliography.bib in place
    python3 paper/scripts/bib_labels.py --check    # only report entries whose label is missing or stale
"""

import re
import sys
import unicodedata
from collections import defaultdict
from pathlib import Path

BIB = Path(__file__).resolve().parent.parent / "bibliography.bib"


def entries(text):
    """Yield (start, end, key, body) for each @type{key, ...} entry, `body` being the text after `key,`."""
    for m in re.finditer(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", text):
        if m.group(1).lower() in ("comment", "string", "preamble"):
            continue
        depth, i = 1, m.end()
        while depth:
            depth += {"{": 1, "}": -1}.get(text[i], 0)
            i += 1
        yield m.start(), i, m.group(2), text[m.end():i - 1]


def field(body, name):
    """The value of field `name` (braces or quotes), or None."""
    m = re.search(r"(?im)^\s*" + name + r"\s*=\s*", body)
    if not m:
        return None
    i = m.end()
    if body[i] == '"':
        return body[i + 1:body.index('"', i + 1)]
    if body[i] != "{":
        return re.match(r"[^,\s]+", body[i:]).group(0)
    depth, j = 1, i + 1
    while depth:
        depth += {"{": 1, "}": -1}.get(body[j], 0)
        j += 1
    return body[i + 1:j - 1]


def split_top(s, sep):
    """Split `s` on the regex `sep`, ignoring matches inside braces."""
    parts, depth, last = [], 0, 0
    for m in re.finditer(r"\{|\}|" + sep, s):
        if m.group(0) == "{":
            depth += 1
        elif m.group(0) == "}":
            depth -= 1
        elif depth == 0:
            parts.append(s[last:m.start()])
            last = m.end()
    parts.append(s[last:])
    return [p.strip() for p in parts]


def plain(s):
    """Drop TeX accents and braces: f{\\"u}r -> fur, B{\\"u}nz -> Bunz (the label only needs letters)."""
    s = re.sub(r"\\[a-zA-Z]+\s*|\\.", "", s)
    s = s.replace("{", "").replace("}", "")
    return unicodedata.normalize("NFC", s)


def last_name(name):
    """(last name, is_organization) of one BibTeX name."""
    name = name.strip()
    if name.startswith("{") and split_top(name, r"\s+") == [name] and name.endswith("}"):
        return plain(name), True  # {Ethereum Foundation}: one braced group
    parts = split_top(name, ",")
    if len(parts) > 1:
        return plain(parts[0]), False  # Last, First
    words = split_top(name, r"\s+")
    # First von Last: the last name starts at the first lowercase word before the final one.
    for k, w in enumerate(words[:-1]):
        if k and plain(w)[:1].islower():
            return plain(" ".join(words[k:])), False
    return plain(words[-1]), False


def letters(s):
    return "".join(c for c in s if c.isalpha())


def base_label(body):
    authors = field(body, "author") or field(body, "editor")
    year = field(body, "year") or (field(body, "date") or "")[:4]
    year = re.sub(r"\D", "", year)[-2:]
    if not authors:
        title = letters(plain(field(body, "title") or "")) or "Anon"
        return title[:3] + year
    names = [last_name(n) for n in split_top(authors, r"\s+and\s+")]
    if len(names) == 1:
        return letters(names[0][0])[:3] + year
    return "".join(letters(n)[:1].upper() for n, _ in names) + year


def main():
    check = "--check" in sys.argv[1:]
    text = BIB.read_text(encoding="utf-8")
    found = list(entries(text))
    groups = defaultdict(list)
    for e in found:
        groups[base_label(e[3])].append(e)
    labels = {}
    for base, es in groups.items():
        for n, e in enumerate(es):
            labels[e[2]] = base + ("abcdefghijklmnopqrstuvwxyz"[n] if len(es) > 1 else "")

    out, pos, stale = [], 0, []
    for start, end, key, body in found:
        label = labels[key]
        if field(body, "abstract") == label:
            continue
        stale.append((key, field(body, "abstract"), label))
        entry = text[start:end]
        if field(body, "abstract") is not None:
            entry = re.sub(r"(?im)^(\s*abstract\s*=\s*)\{[^{}]*\}", lambda m: m.group(1) + "{" + label + "}", entry, count=1)
        else:
            head = re.match(r"@\w+\s*\{\s*[^,\s]+\s*,\s*?\n", entry).group(0)
            indent = re.match(r"[ \t]*", entry[len(head):]).group(0) or "  "
            entry = head + indent + "abstract = {" + label + "},\n" + entry[len(head):]
        out.append(text[pos:start] + entry)
        pos = end
    out.append(text[pos:])

    for key, old, new in stale:
        print(f"{key}: {old or '(none)'} -> {new}")
    if check:
        sys.exit(1 if stale else 0)
    if stale:
        BIB.write_text("".join(out), encoding="utf-8")
    print(f"{len(found)} entries, {len(stale)} label(s) {'written' if stale else 'already up to date'}.")


if __name__ == "__main__":
    main()
