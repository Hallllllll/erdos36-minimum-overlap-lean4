#!/usr/bin/env python3
"""Generate deterministic paper metrics from the checked-in proof data."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import re
import sys
import tokenize
from fractions import Fraction
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "paper" / "generated"
METRICS_JSON = GENERATED / "metrics.json"
METRICS_TEX = GENERATED / "metrics.tex"
PACKING_BASE_EXPONENT = 128

TEX_MACROS = {
    "all_lean_code_loc": "MetricAllLeanCodeLOC",
    "all_lean_source_loc": "MetricAllLeanSourceLOC",
    "bound_decimal_lower": "MetricBoundDecimalLower",
    "bound_decimal_upper": "MetricBoundDecimalUpper",
    "bound_denominator": "MetricBoundDenominator",
    "bound_denominator_bits": "MetricBoundDenominatorBits",
    "bound_fraction": "MetricBoundFraction",
    "bound_numerator": "MetricBoundNumerator",
    "bound_numerator_bits": "MetricBoundNumeratorBits",
    "carry_free_base_threshold": "MetricCarryFreeBaseThreshold",
    "carry_free_base_threshold_bits": "MetricCarryFreeBaseThresholdBits",
    "coefficient_upper_bound": "MetricCoefficientUpperBound",
    "coefficient_upper_bound_bits": "MetricCoefficientUpperBoundBits",
    "gain_decimal_lower": "MetricGainDecimalLower",
    "gain_decimal_upper": "MetricGainDecimalUpper",
    "gain_denominator": "MetricGainDenominator",
    "gain_denominator_bits": "MetricGainDenominatorBits",
    "gain_fraction": "MetricGainFraction",
    "gain_numerator": "MetricGainNumerator",
    "gain_numerator_bits": "MetricGainNumeratorBits",
    "generated_lean_code_loc": "MetricGeneratedLeanCodeLOC",
    "generated_lean_source_loc": "MetricGeneratedLeanSourceLOC",
    "handwritten_lean_code_loc": "MetricHandwrittenLeanCodeLOC",
    "handwritten_lean_source_loc": "MetricHandwrittenLeanSourceLOC",
    "integer_peak_bits": "MetricIntegerPeakBits",
    "lean_theorem_declarations": "MetricLeanTheoremDeclarations",
    "packed_base_exponent": "MetricPackedBaseExponent",
    "packed_fixed_storage_bits": "MetricPackedFixedStorageBits",
    "packed_left_operand_bits": "MetricPackedLeftOperandBits",
    "packed_left_storage_headroom_bits": "MetricPackedLeftStorageHeadroomBits",
    "packed_product_bits": "MetricPackedProductBits",
    "packed_right_operand_bits": "MetricPackedRightOperandBits",
    "packed_right_storage_headroom_bits": "MetricPackedRightStorageHeadroomBits",
    "parent_bound_denominator": "MetricParentBoundDenominator",
    "parent_bound_denominator_bits": "MetricParentBoundDenominatorBits",
    "parent_bound_fraction": "MetricParentBoundFraction",
    "parent_bound_numerator": "MetricParentBoundNumerator",
    "parent_bound_numerator_bits": "MetricParentBoundNumeratorBits",
    "parent_cells": "MetricParentCells",
    "parent_signed_vertices": "MetricParentSignedVertices",
    "peak_event_index": "MetricPeakEventIndex",
    "peak_signed_vertex_index": "MetricPeakSignedVertexIndex",
    "python_verifier_code_loc": "MetricPythonVerifierCodeLOC",
    "python_verifier_source_loc": "MetricPythonVerifierSourceLOC",
    "small_case_count": "MetricSmallCaseCount",
    "small_case_partition_count": "MetricSmallCasePartitionCount",
    "witness_cells": "MetricWitnessCells",
    "witness_denominator": "MetricWitnessDenominator",
    "witness_denominator_bits": "MetricWitnessDenominatorBits",
    "witness_event_count": "MetricWitnessEventCount",
    "witness_distinct_heights": "MetricWitnessDistinctHeights",
    "witness_height_max": "MetricWitnessHeightMax",
    "witness_height_sum": "MetricWitnessHeightSum",
    "witness_peak_count": "MetricWitnessPeakCount",
    "witness_peak_lag": "MetricWitnessPeakLag",
    "witness_signed_vertices": "MetricWitnessSignedVertices",
    "witness_shift_denominator": "MetricWitnessShiftDenominator",
    "witness_shift_fraction": "MetricWitnessShiftFraction",
    "witness_shift_numerator": "MetricWitnessShiftNumerator",
}


class MetricsError(ValueError):
    """Raised when checked-in inputs do not satisfy the metrics contract."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise MetricsError(message)


def read_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def ratio_metrics(prefix: str, value: Fraction) -> dict[str, int | str]:
    return {
        f"{prefix}_numerator": str(value.numerator),
        f"{prefix}_denominator": str(value.denominator),
        f"{prefix}_numerator_bits": value.numerator.bit_length(),
        f"{prefix}_denominator_bits": value.denominator.bit_length(),
        f"{prefix}_fraction": rf"\frac{{{value.numerator}}}{{{value.denominator}}}",
    }


def horner_pack(values: Iterable[int], exponent: int) -> int:
    packed = 0
    for value in reversed(tuple(values)):
        packed = (packed << exponent) | value
    return packed


def shifted_sum_pack(values: Iterable[int], exponent: int) -> int:
    return sum(value << (exponent * index) for index, value in enumerate(values))


def lean_code_lines(text: str) -> int:
    count = 0
    comment_depth = 0
    for line in text.splitlines():
        has_code = False
        index = 0
        while index < len(line):
            if comment_depth:
                if line.startswith("/-", index):
                    comment_depth += 1
                    index += 2
                elif line.startswith("-/", index):
                    comment_depth -= 1
                    index += 2
                else:
                    index += 1
            elif line.startswith("--", index):
                break
            elif line.startswith("/-", index):
                comment_depth += 1
                index += 2
            else:
                if not line[index].isspace():
                    has_code = True
                index += 1
        if has_code:
            count += 1
    return count


def python_code_lines(text: str) -> int:
    code_lines: set[int] = set()
    ignored = {
        tokenize.ENCODING,
        tokenize.ENDMARKER,
        tokenize.NEWLINE,
        tokenize.NL,
        tokenize.INDENT,
        tokenize.DEDENT,
        tokenize.COMMENT,
    }
    for token in tokenize.generate_tokens(io.StringIO(text).readline):
        if token.type not in ignored and token.string.strip():
            code_lines.update(range(token.start[0], token.end[0] + 1))
    return len(code_lines)


def source_loc(paths: Iterable[Path], extension: str) -> tuple[int, int]:
    physical = 0
    code = 0
    for path in paths:
        text = path.read_text(encoding="utf-8")
        physical += len(text.splitlines())
        if extension == ".lean":
            code += lean_code_lines(text)
        elif extension == ".py":
            code += python_code_lines(text)
        else:
            raise MetricsError(f"Unsupported LOC extension: {extension}")
    return physical, code


def collect_metrics(root: Path = ROOT) -> dict[str, int | str]:
    construction_bytes = (root / "construction.json").read_bytes()
    construction = read_json(root / "construction.json")
    certificate = read_json(root / "certificate.json")
    parent_values = [
        int(value)
        for value in (root / "sources" / "frontier_parent.txt").read_text().split()
    ]
    small_cases = read_json(root / "small_cases.json")

    require(isinstance(construction, dict), "construction.json root")
    require(isinstance(certificate, dict), "certificate.json root")
    require(isinstance(small_cases, list), "small_cases.json root")

    numerators = construction["numerators"]
    denominator = construction["denominator"]
    cells = len(numerators)
    require(type(denominator) is int and denominator > 0, "witness denominator")
    require(cells > 0, "witness cells")
    require(
        all(type(value) is int and 0 <= value <= denominator for value in numerators),
        "witness heights",
    )
    require(2 * sum(numerators) == cells * denominator, "witness mass")
    require(cells == certificate["grid_cells"], "grid cell count")
    require(denominator == certificate["denominator"], "grid denominator")
    require(Fraction(certificate["integral"]) == 1, "certificate integral")
    require(
        hashlib.sha256(construction_bytes).hexdigest()
        == certificate["construction_sha256"],
        "construction digest",
    )

    parent_denominator, *parent_heights = parent_values
    parent_cells = len(parent_heights)
    require(parent_cells > 0, "parent cells")
    require(
        hashlib.sha256((root / "sources" / "frontier_parent.txt").read_bytes()).hexdigest()
        == certificate["parent_sha256"],
        "parent digest",
    )

    event_count = 2 * cells - 1
    signed_vertices = event_count + 2
    require(certificate["peak_lags"] == [-2284], "unique peak lag")
    peak_lag = certificate["peak_lags"][0]
    peak_event_index = cells - 1 + peak_lag
    peak_signed_vertex_index = peak_lag + cells
    require(
        peak_event_index == 7123 and peak_signed_vertex_index == 7124,
        "peak indices",
    )
    shift = Fraction(2 * peak_lag, cells)

    bound = Fraction(certificate["cap"])
    parent_bound = Fraction(certificate["parent_cap"])
    gain = Fraction(certificate["gain"])
    require(parent_bound - bound == gain, "bound gain")
    require(
        bound < Fraction("0.38085601258978320592"),
        "advertised strict upper bound",
    )

    coefficient_upper_bound = cells * denominator * denominator
    carry_free_threshold = cells * cells * denominator * denominator
    require((1 << PACKING_BASE_EXPONENT) > carry_free_threshold, "carry-free base")

    complements = [denominator - value for value in reversed(numerators)]
    left_packed = horner_pack(numerators, PACKING_BASE_EXPONENT)
    right_packed = horner_pack(complements, PACKING_BASE_EXPONENT)
    require(
        left_packed == shifted_sum_pack(numerators, PACKING_BASE_EXPONENT),
        "left direct packing",
    )
    require(
        right_packed == shifted_sum_pack(complements, PACKING_BASE_EXPONENT),
        "right direct packing",
    )

    product = left_packed * right_packed
    limb_bytes = PACKING_BASE_EXPONENT // 8
    product_raw = product.to_bytes(event_count * limb_bytes, "little")
    events = [
        int.from_bytes(product_raw[index : index + limb_bytes], "little")
        for index in range(0, len(product_raw), limb_bytes)
    ]
    require(len(events) == event_count, "packed event count")
    require(max(events) == int(certificate["integer_peak"]), "packed event peak")
    event_digest = hashlib.sha256(
        "".join(f"{value}\n" for value in [0, *events, 0]).encode("ascii")
    ).hexdigest()
    require(event_digest == certificate["event_sha256"], "packed event digest")

    lean_paths = sorted((root / "Overlap").glob("*.lean"))
    generated_lean_paths = [
        path for path in lean_paths if path.name in {"Bench.lean", "Data.lean"}
    ]
    handwritten_lean_paths = [
        path for path in lean_paths if path.name not in {"Bench.lean", "Data.lean"}
    ]
    handwritten_lean_paths.append(root / "Overlap.lean")
    all_lean_paths = [*lean_paths, root / "Overlap.lean"]
    python_verifier_paths = [
        root / "verify.py",
        root / "audit_verify.py",
    ]

    all_lean_physical, all_lean_code = source_loc(all_lean_paths, ".lean")
    handwritten_physical, handwritten_code = source_loc(
        handwritten_lean_paths, ".lean"
    )
    verifier_physical, verifier_code = source_loc(
        python_verifier_paths, ".py"
    )
    theorem_pattern = re.compile(
        r"^(?:[ \t]*@\[[^\n]*\][ \t]*)?[ \t]*theorem"
        r"\s+[A-Za-z_][A-Za-z0-9_]*",
        re.MULTILINE,
    )
    theorem_declarations = sum(
        len(theorem_pattern.findall(path.read_text(encoding="utf-8")))
        for path in handwritten_lean_paths
    )

    small_case_partition_count = sum(
        sum(case["hist"].values()) for case in small_cases
    )
    require(small_case_partition_count == 17576, "small-case partition count")

    metrics: dict[str, int | str] = {
        "schema_version": 1,
        "loc_definition": (
            "Source LOC is physical line count. Code LOC excludes blank, "
            "comment-only, and block-comment-only lines."
        ),
        "packing_width_method": (
            "Bit lengths of base-2^128 operands computed independently by "
            "Horner accumulation and shifted-sum evaluation."
        ),
        "construction_sha256": certificate["construction_sha256"],
        "parent_sha256": certificate["parent_sha256"],
        "event_sha256": certificate["event_sha256"],
        "witness_cells": cells,
        "witness_denominator": denominator,
        "witness_denominator_bits": denominator.bit_length(),
        "witness_event_count": event_count,
        "witness_signed_vertices": signed_vertices,
        "witness_peak_lag": peak_lag,
        "witness_peak_count": len(certificate["peak_lags"]),
        "peak_event_index": peak_event_index,
        "peak_signed_vertex_index": peak_signed_vertex_index,
        "witness_shift_numerator": shift.numerator,
        "witness_shift_denominator": shift.denominator,
        "witness_shift_fraction": (
            rf"-\frac{{{-shift.numerator}}}{{{shift.denominator}}}"
            if shift < 0
            else rf"\frac{{{shift.numerator}}}{{{shift.denominator}}}"
        ),
        "witness_height_sum": sum(numerators),
        "witness_height_min": min(numerators),
        "witness_height_max": max(numerators),
        "witness_distinct_heights": len(set(numerators)),
        "integer_peak_bits": int(certificate["integer_peak"]).bit_length(),
        "bound_decimal_lower": certificate["cap_interval"][0],
        "bound_decimal_upper": certificate["cap_interval"][1],
        "gain_decimal_lower": certificate["gain_interval"][0],
        "gain_decimal_upper": certificate["gain_interval"][1],
        "parent_cells": parent_cells,
        "parent_signed_vertices": 2 * parent_cells + 1,
        "coefficient_upper_bound": str(coefficient_upper_bound),
        "coefficient_upper_bound_bits": coefficient_upper_bound.bit_length(),
        "carry_free_base_threshold": str(carry_free_threshold),
        "carry_free_base_threshold_bits": carry_free_threshold.bit_length(),
        "packed_base_exponent": PACKING_BASE_EXPONENT,
        "packed_fixed_storage_bits": cells * PACKING_BASE_EXPONENT,
        "packed_left_operand_bits": left_packed.bit_length(),
        "packed_right_operand_bits": right_packed.bit_length(),
        "packed_left_storage_headroom_bits": (
            cells * PACKING_BASE_EXPONENT - left_packed.bit_length()
        ),
        "packed_right_storage_headroom_bits": (
            cells * PACKING_BASE_EXPONENT - right_packed.bit_length()
        ),
        "packed_product_bits": product.bit_length(),
        "small_case_count": len(small_cases),
        "small_case_partition_count": small_case_partition_count,
        "lean_theorem_declarations": theorem_declarations,
        "all_lean_source_loc": all_lean_physical,
        "all_lean_code_loc": all_lean_code,
        "handwritten_lean_source_loc": handwritten_physical,
        "handwritten_lean_code_loc": handwritten_code,
        "generated_lean_source_loc": sum(
            len(path.read_text(encoding="utf-8").splitlines())
            for path in generated_lean_paths
        ),
        "generated_lean_code_loc": sum(
            lean_code_lines(path.read_text(encoding="utf-8"))
            for path in generated_lean_paths
        ),
        "python_verifier_source_loc": verifier_physical,
        "python_verifier_code_loc": verifier_code,
    }
    metrics.update(ratio_metrics("bound", bound))
    metrics.update(ratio_metrics("parent_bound", parent_bound))
    metrics.update(ratio_metrics("gain", gain))
    require(set(TEX_MACROS).issubset(metrics), "TeX macro source keys")
    return dict(sorted(metrics.items()))


def render_json(metrics: dict[str, int | str]) -> str:
    return json.dumps(metrics, indent=2, sort_keys=True) + "\n"


def render_tex(metrics: dict[str, int | str]) -> str:
    lines = [
        "% Generated by paper/metrics.py. Do not edit by hand.",
        "% Regenerate with: python3 paper/metrics.py",
    ]
    for key, macro in sorted(TEX_MACROS.items(), key=lambda item: item[1]):
        value = metrics[key]
        lines.append(rf"\newcommand{{\{macro}}}{{{value}}}")
    return "\n".join(lines) + "\n"


def write_if_changed(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_text(encoding="utf-8") == text:
        return
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(text, encoding="utf-8", newline="\n")
    temporary.replace(path)


def generate(root: Path = ROOT, check: bool = False) -> dict[str, int | str]:
    metrics = collect_metrics(root)
    outputs = {
        root / "paper" / "generated" / "metrics.json": render_json(metrics),
        root / "paper" / "generated" / "metrics.tex": render_tex(metrics),
    }
    if check:
        stale = [
            path
            for path, text in outputs.items()
            if not path.exists() or path.read_text(encoding="utf-8") != text
        ]
        if stale:
            names = ", ".join(str(path.relative_to(root)) for path in stale)
            raise MetricsError(f"Generated metrics are stale: {names}")
    else:
        for path, text in outputs.items():
            write_if_changed(path, text)
    return metrics


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify that generated files are current without writing them",
    )
    args = parser.parse_args(argv)
    try:
        metrics = generate(check=args.check)
    except MetricsError as error:
        print(f"metrics error: {error}", file=sys.stderr)
        return 1
    action = "verified" if args.check else "generated"
    print(
        f"{action} {METRICS_JSON.relative_to(ROOT)} and "
        f"{METRICS_TEX.relative_to(ROOT)} ({len(metrics)} metrics)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
