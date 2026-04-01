#!/usr/bin/env python3
"""
Mechanical pattern checker for Lean 4 proof files.

Each finding is tagged with a safety level:
  [AUTO]   — pure text replacement, safe without LSP
  [VERIFY] — likely correct but MUST be verified with lean_diagnostic_messages

Usage:
    python3 check_patterns.py <file.lean>
    python3 check_patterns.py <directory> --recursive
"""

import re
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List


@dataclass
class Finding:
    file: str
    line: int
    pattern: str
    safety: str  # "AUTO" or "VERIFY"
    message: str
    snippet: str


# ── AUTO-SAFE patterns (pure text replacement) ──────────────────────

def check_push_neg_deprecated(lines: List[str], path: str) -> List[Finding]:
    """push_neg → push Not (deprecated tactic)."""
    findings = []
    for i, line in enumerate(lines):
        if line.strip().startswith('--') or line.strip().startswith('/-'):
            continue
        code = re.sub(r'--.*$', '', line)
        if re.search(r'\bpush_neg\b', code):
            findings.append(Finding(path, i + 1, "push_neg→push-Not",
                "AUTO",
                "`push_neg` is deprecated — use `push Not`",
                line.strip()))
    return findings


def check_consecutive_blanks(lines: List[str], path: str) -> List[Finding]:
    """Two or more consecutive blank lines."""
    findings = []
    i = 0
    while i < len(lines):
        if lines[i].strip() == '':
            j = i + 1
            while j < len(lines) and lines[j].strip() == '':
                j += 1
            if j - i >= 2:
                findings.append(Finding(path, i + 1, "consecutive-blanks",
                    "AUTO",
                    f"{j - i} consecutive blank lines — collapse to one", ""))
            i = j
        else:
            i += 1
    return findings


def check_long_lines(lines: List[str], path: str) -> List[Finding]:
    """Lines exceeding 100 Unicode codepoints."""
    findings = []
    for i, line in enumerate(lines):
        l = line.rstrip('\n')
        if len(l) > 100:
            findings.append(Finding(path, i + 1, "long-line",
                "AUTO",
                f"Line is {len(l)} codepoints (limit 100)",
                l[:100] + "…"))
    return findings


def check_duplicate_open(lines: List[str], path: str) -> List[Finding]:
    """Duplicate `open` declarations."""
    findings = []
    opens: dict[str, int] = {}
    for i, line in enumerate(lines):
        s = line.strip()
        m = re.match(r'open\s+(.+?)(?:\s+in\s*$|\s*$)', s)
        if m and not s.startswith('--'):
            key = m.group(1).strip()
            if key in opens:
                findings.append(Finding(path, i + 1, "duplicate-open",
                    "AUTO",
                    f"Duplicate `open {key}` (first at line {opens[key]})", s))
            else:
                opens[key] = i + 1
    return findings


def check_grind_symm(lines: List[str], path: str) -> List[Finding]:
    """grind [lemma.symm] → grind [lemma] (grind handles symmetry)."""
    findings = []
    for i, line in enumerate(lines):
        s = line.strip()
        if re.search(r'\bgrind\s*\[.*\.symm\b', s):
            findings.append(Finding(path, i + 1, "grind-symm",
                "AUTO",
                "`grind` handles symmetry internally — drop `.symm`", s))
    return findings


# ── VERIFY-REQUIRED patterns (need LSP confirmation) ────────────────

def check_rw_exact(lines: List[str], path: str) -> List[Finding]:
    """rw [...]; exact h → rwa [...] (ONLY for bare hypotheses)."""
    findings = []
    for i, line in enumerate(lines):
        s = line.strip()
        # Single-line: rw [...]; exact ...  (no `at` clause on the rw)
        m = re.search(r'\brw\s*\[([^\]]*)\]\s*;\s*exact\s+(\S+)', s)
        if m and not re.search(r'\bat\b', s.split(';')[0]):
            exact_term = m.group(2)
            # Only flag if exact term looks like a bare hypothesis (simple identifier)
            if re.match(r'^[a-zA-Z_]\w*$', exact_term):
                findings.append(Finding(path, i + 1, "rw+exact→rwa",
                    "VERIFY",
                    f"Possibly `rwa` — verify `{exact_term}` is a local hypothesis",
                    s))
        # Two-line: rw [...] then exact on next line (no `at` clause)
        if re.match(r'rw\s*\[', s) and not re.search(r'\bat\b', s):
            if i + 1 < len(lines):
                ns = lines[i + 1].strip()
                m2 = re.match(r'exact\s+(\S+)$', ns)
                if m2:
                    exact_term = m2.group(1)
                    if re.match(r'^[a-zA-Z_]\w*$', exact_term):
                        findings.append(Finding(path, i + 1, "rw+exact→rwa",
                            "VERIFY",
                            f"Possibly `rwa` — verify `{exact_term}` is a local hypothesis",
                            f"{s}  /  {ns}"))
    return findings


def check_by_exact(lines: List[str], path: str) -> List[Finding]:
    """:= by exact t → := t"""
    findings = []
    for i, line in enumerate(lines):
        s = line.strip()
        if re.search(r':=\s*by\s+exact\b', s):
            findings.append(Finding(path, i + 1, "by-exact",
                "VERIFY",
                "`:= by exact t` → `:= t`", s))
        # Two-line: := by on one line, exact on next (single tactic)
        if re.search(r':=\s*by\s*$', s) and i + 1 < len(lines):
            ns = lines[i + 1].strip()
            if re.match(r'exact\b', ns):
                is_single = True
                if i + 2 < len(lines):
                    next_line = lines[i + 2]
                    next_stripped = next_line.strip()
                    if next_stripped and not next_stripped.startswith('--'):
                        tactic_indent = len(lines[i + 1]) - len(lines[i + 1].lstrip())
                        next_indent = len(next_line) - len(next_line.lstrip())
                        if next_indent >= tactic_indent:
                            is_single = False
                if is_single:
                    findings.append(Finding(path, i + 1, "by-exact",
                        "VERIFY",
                        "`:= by` + single `exact` → `:= t`",
                        f"{s}  /  {ns}"))
    return findings


def check_consecutive_rw(lines: List[str], path: str) -> List[Finding]:
    """Consecutive rw calls that could be merged."""
    findings = []
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if re.match(r'rw\s*\[', s) and not re.search(r'\bat\b', s):
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or
                                       lines[j].strip().startswith('--')):
                j += 1
            if j < len(lines):
                ns = lines[j].strip()
                if re.match(r'rw\s*\[', ns) and not re.search(r'\bat\b', ns):
                    indent_i = len(lines[i]) - len(lines[i].lstrip())
                    indent_j = len(lines[j]) - len(lines[j].lstrip())
                    if indent_i == indent_j:
                        findings.append(Finding(path, i + 1, "consecutive-rw",
                            "VERIFY",
                            "Consecutive `rw` calls — may be mergeable",
                            f"{s}  /  {ns}"))
                        i = j + 1
                        continue
        i += 1
    return findings


def check_simp_inside_simpa(lines: List[str], path: str) -> List[Finding]:
    """simp [...]; simpa [...] → just simpa [...]"""
    findings = []
    for i, line in enumerate(lines):
        s = line.strip()
        if re.search(r'\bsimp\b.*;\s*simpa\b', s):
            findings.append(Finding(path, i + 1, "simp+simpa",
                "VERIFY",
                "Redundant `simp` before `simpa` — `simpa` already runs `simp`", s))
        if re.match(r'simp\b', s) and not s.startswith('simpa') and i + 1 < len(lines):
            ns = lines[i + 1].strip()
            if re.match(r'simpa\b', ns):
                findings.append(Finding(path, i + 1, "simp+simpa",
                    "VERIFY",
                    "Redundant `simp` before `simpa`",
                    f"{s}  /  {ns}"))
    return findings


def check_have_exact_this(lines: List[str], path: str) -> List[Finding]:
    """have h := ...; exact h → inline the expression."""
    findings = []
    for i, line in enumerate(lines):
        s = line.strip()
        m = re.match(r'have\s+(\w+)\s*:?=', s)
        if m:
            name = m.group(1)
            for j in range(i + 1, min(i + 4, len(lines))):
                ns = lines[j].strip()
                if not ns or ns.startswith('--'):
                    continue
                if ns == f'exact {name}':
                    findings.append(Finding(path, i + 1, "have+exact",
                        "VERIFY",
                        f"Inline `have {name}` — used only as `exact {name}`",
                        f"{s}  /  {ns}"))
                break
    return findings


ALL_CHECKS = [
    # AUTO-SAFE
    check_push_neg_deprecated,
    check_consecutive_blanks,
    check_long_lines,
    check_duplicate_open,
    check_grind_symm,
    # VERIFY-REQUIRED
    check_rw_exact,
    check_by_exact,
    check_consecutive_rw,
    check_simp_inside_simpa,
    check_have_exact_this,
]


def analyze_file(path: Path) -> List[Finding]:
    with open(path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    findings = []
    for check in ALL_CHECKS:
        findings.extend(check(lines, str(path)))
    findings.sort(key=lambda f: f.line)
    return findings


def main():
    import argparse
    parser = argparse.ArgumentParser(
        description='Check Lean 4 files for mechanical improvement patterns')
    parser.add_argument('path', help='Lean file or directory')
    parser.add_argument('--recursive', '-r', action='store_true',
                        help='Recurse into subdirectories')
    parser.add_argument('--pattern', '-p', action='append',
                        help='Only run specific pattern(s)')
    parser.add_argument('--auto-only', action='store_true',
                        help='Only show AUTO-safe findings')
    args = parser.parse_args()

    path = Path(args.path)
    if not path.exists():
        print(f"Error: {path} does not exist", file=sys.stderr)
        return 1

    if path.is_file():
        files = [path]
    elif args.recursive:
        files = sorted(path.rglob('*.lean'))
    else:
        files = sorted(path.glob('*.lean'))

    if not files:
        print(f"No .lean files found in {path}", file=sys.stderr)
        return 1

    total = 0
    by_pattern: dict[str, int] = {}
    auto_count = 0
    verify_count = 0
    for f in files:
        findings = analyze_file(f)
        if args.pattern:
            findings = [fd for fd in findings if fd.pattern in args.pattern]
        if args.auto_only:
            findings = [fd for fd in findings if fd.safety == "AUTO"]
        if findings:
            for fd in findings:
                print(f"{fd.file}:{fd.line}: [{fd.safety}] [{fd.pattern}] {fd.message}")
                if fd.snippet:
                    print(f"  {fd.snippet}")
                by_pattern[fd.pattern] = by_pattern.get(fd.pattern, 0) + 1
                total += 1
                if fd.safety == "AUTO":
                    auto_count += 1
                else:
                    verify_count += 1

    if total:
        print(f"\n{'='*60}")
        print(f"Total: {total} finding(s) across {len(files)} file(s)")
        print(f"  AUTO (safe to fix without LSP): {auto_count}")
        print(f"  VERIFY (needs LSP confirmation): {verify_count}")
        print()
        for pat, count in sorted(by_pattern.items(), key=lambda x: -x[1]):
            print(f"  {pat}: {count}")
    else:
        print(f"No findings in {len(files)} file(s).")

    return 1 if total else 0


if __name__ == '__main__':
    sys.exit(main())
