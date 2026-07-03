#!/usr/bin/env python3
"""Cell-by-cell diff of dl2002_data in dls.v against the published Standard Edition table extracted from a regulations PDF (ICC/ECB); exits nonzero on any mismatch or on internal inconsistency between the PDF's own sheets."""
import re
import subprocess
import sys

def parse_pdf(path):
    txt = subprocess.run(["pdftotext", "-layout", path, "-"],
                         capture_output=True, text=True, check=True).stdout
    rows, clashes = {}, 0
    for line in txt.splitlines():
        toks = line.split()
        if len(toks) < 11 or not re.fullmatch(r"\d{1,2}(\.\d)?", toks[0]):
            continue
        vals = toks[1:11]
        if not all(re.fullmatch(r"\d{1,3}\.\d", v) for v in vals):
            continue
        ov, _, ball = toks[0].partition(".")
        balls = int(ov) * 6 + int(ball or 0)
        cells = [round(float(v) * 10) for v in vals]
        if balls in rows and rows[balls] != cells:
            clashes += 1
            print(f"PDF INTERNAL CLASH at {balls} balls: {rows[balls]} vs {cells}")
        rows[balls] = cells
    return rows, clashes

def parse_dls(path):
    src = open(path).read()
    i = src.index("Definition dl2002_data")
    j = src.index("].", i)
    return [[int(x) for x in re.findall(r"\d+", r)]
            for r in re.findall(r"\[([\d;\s]+)\]", src[i:j])]

def main():
    if len(sys.argv) < 2:
        sys.exit("usage: diff_table.py REGULATIONS_PDF [DLS_V]")
    pdf_rows, clashes = parse_pdf(sys.argv[1])
    v_rows = parse_dls(sys.argv[2] if len(sys.argv) > 2 else "dls.v")
    mismatches = checked = 0
    for balls in sorted(pdf_rows):
        for w in range(10):
            checked += 1
            if v_rows[balls][w] != pdf_rows[balls][w]:
                mismatches += 1
                print(f"MISMATCH balls={balls} w={w}: dls.v={v_rows[balls][w]} pdf={pdf_rows[balls][w]}")
    missing = sorted(set(range(301)) - set(pdf_rows))
    print(f"{checked} cells compared over {len(pdf_rows)} PDF rows; "
          f"{mismatches} mismatches; {clashes} internal clashes; "
          f"rows absent from PDF: {missing if missing else 'none'}")
    sys.exit(0 if mismatches == 0 and clashes == 0 and len(pdf_rows) >= 300 else 1)

if __name__ == "__main__":
    main()
