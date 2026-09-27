"""Split the combined draft file into one file per draft item.

Each output file obeys the platform draft layout: first line exactly `import Mathlib`,
then a `namespace`/`end` block containing exactly one theorem with exactly one
occurrence of the single-line string `:= by sorry`. The leading doc comment of each
theorem is kept; nothing belonging to another theorem is carried over.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "All.lean"
NAMESPACE = "EqualTwoSquares"


def blocks(text: str) -> list[tuple[str, str]]:
    """Return (name, chunk) pairs: each chunk is one theorem with its doc comment."""
    lines = text.split("\n")
    out: list[tuple[str, str]] = []
    pending: list[str] = []
    current: list[str] | None = None
    name = ""
    in_comment = False

    def flush() -> None:
        nonlocal current
        if current is not None:
            out.append((name, "\n".join(current).rstrip()))
            current = None

    for line in lines:
        stripped = line.strip()
        if stripped.startswith("/--") or stripped.startswith("/-!"):
            flush()
            in_comment = not stripped.endswith("-/")
            pending.append(line)
            continue
        if in_comment:
            pending.append(line)
            if stripped.endswith("-/"):
                in_comment = False
            continue
        if stripped.startswith("theorem "):
            flush()
            name = stripped[len("theorem "):].split()[0]
            current = pending + [line]
            pending = []
            continue
        if stripped.startswith("end "):
            flush()
            continue
        if stripped:
            (current if current is not None else pending).append(line)
    flush()
    return out


def main() -> None:
    text = SRC.read_text(encoding="utf-8")
    if not text.startswith("import Mathlib\n"):
        raise SystemExit("%s: first line must be exactly `import Mathlib`" % SRC)
    body = text.split("namespace %s" % NAMESPACE, 1)[1]
    body = body.rsplit("\nend %s" % NAMESPACE, 1)[0]

    outdir = HERE / "items"
    outdir.mkdir(exist_ok=True)
    names: list[str] = []
    for name, chunk in blocks(body):
        lines = [ln for ln in chunk.split("\n") if ln.strip() != "namespace %s" % NAMESPACE]
        text_out = ("import Mathlib\n\nnamespace %s\n\n" % NAMESPACE
                    + "\n".join(lines).strip("\n")
                    + "\n\nend %s\n" % NAMESPACE)
        if text_out.count(":= by sorry") != 1:
            raise SystemExit("wrong number of sorry markers for %s" % name)
        if text_out.count("theorem ") != 1:
            raise SystemExit("more than one theorem in the item file for %s" % name)
        (outdir / ("%s.lean" % name)).write_text(text_out, encoding="utf-8")
        names.append(name)
    print("%d item files written:" % len(names))
    for name in names:
        print("  ", name)


if __name__ == "__main__":
    main()
