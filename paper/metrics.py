#!/usr/bin/env python3
"""Generate deterministic paper metrics from the checked-in proof data."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import re
import subprocess
import sys
import tokenize
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN
from fractions import Fraction
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "paper" / "generated"
METRICS_JSON = GENERATED / "metrics.json"
METRICS_TEX = GENERATED / "metrics.tex"
PACKING_BASE_EXPONENT = 128
LINUX_SCALING = Path(
    "benchmarks/results/linux-canonical-scaling-combined-20261127T070821Z"
)
LINUX_UPGRADED = Path(
    "benchmarks/results/linux-authoritative-final-20261127T070950Z"
)
LINUX_MATCHED = Path("benchmarks/results/linux-matched-v100-045d628")
LINUX_FRESH = Path("benchmarks/results/linux-fresh-root")
LINUX_CONFIRMED = Path("benchmarks/results/linux-confirmed-module-gate")
LINUX_CORE_REPLAYS = (
    "Tree",
    "Data",
    "Numerical",
    "Algebra",
    "AffineBridge",
    "Profile",
    "Spec",
    "Main",
)
LINUX_UPGRADED_MODULES = {
    "Tree",
    "PackedConvolution",
    "ConvolutionExample",
    "Data",
    "Numerical",
    "Algebra",
    "AffineBridge",
    "Profile",
    "Spec",
    "Main",
    "QuarticRounding",
    "CellApprox",
    "GridLower",
    "LagRounding",
    "DiscreteUpper",
    "Bench",
}

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


def read_tsv(path: Path) -> list[dict[str, str]]:
    require(path.is_file(), f"missing TSV input: {path}")
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    require(bool(rows), f"empty TSV input: {path}")
    return rows


def decimal_seconds(value: str | Decimal, label: str) -> Decimal:
    """Parse a clock field without passing through binary floating point."""
    try:
        seconds = Decimal(value)
    except (InvalidOperation, TypeError, ValueError) as error:
        raise MetricsError(f"invalid benchmark seconds at {label}: {value!r}") from error
    require(
        seconds.is_finite() and seconds >= 0,
        f"invalid benchmark seconds at {label}: {value!r}",
    )
    return seconds


def summed_seconds_at_precision(
    values: Iterable[str | Decimal],
    decimal_places: int,
    label: str,
) -> Decimal:
    """Sum exact decimal clocks, then round at the displayed precision."""
    total = sum((decimal_seconds(value, label) for value in values), Decimal(0))
    quantum = Decimal(1).scaleb(-decimal_places)
    return total.quantize(quantum, rounding=ROUND_HALF_EVEN)


def verify_sha256_manifest(root: Path, path: Path) -> None:
    require(path.is_file(), f"missing SHA-256 manifest: {path}")
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        digest, separator, relative = line.partition("  ")
        require(
            bool(separator) and bool(relative),
            f"malformed digest at {path}:{line_number}",
        )
        source = root / relative
        require(source.is_file(), f"missing hashed input: {relative}")
        require(
            hashlib.sha256(source.read_bytes()).hexdigest() == digest,
            f"SHA-256 mismatch: {relative}",
        )


def validate_linux_artifacts(root: Path) -> None:
    scaling = root / LINUX_SCALING
    source_runs = read_tsv(scaling / "SOURCES.tsv")
    expected_rows: list[dict[str, str]] = []
    for source in source_runs:
        source_run = root / source["source_run"]
        raw_rows = read_tsv(source_run / "measurements.tsv")
        for row in raw_rows:
            for key in ("raw_log", "time_log", "cgroup_log"):
                relative = row.get(key, "")
                if relative:
                    require(
                        (source_run / relative).is_file(),
                        f"missing raw Linux input: {source_run / relative}",
                    )
            normalized = dict(row)
            if normalized["status"] in {"timeout", "oom"}:
                normalized["max_rss_kib"] = ""
            expected_rows.append(normalized)
    require(
        read_tsv(scaling / "measurements.tsv") == expected_rows,
        "combined Linux scaling TSV does not match its raw source runs",
    )

    pair_rows = {
        int(row["size_cells"]): row
        for row in read_tsv(scaling / "pair_summary.tsv")
    }
    expected_pairs = {
        128: ("pass", "pass"),
        256: ("pass", "pass"),
        512: ("pass", "pass"),
        1024: ("timeout", "pass"),
        2048: ("not_attempted", "pass"),
    }
    require(set(pair_rows) == set(expected_pairs), "Linux pair-size set mismatch")
    for cells, (direct, packed) in expected_pairs.items():
        require(
            pair_rows[cells]["direct_status"] == direct
            and pair_rows[cells]["packed_status"] == packed,
            f"Linux pair status mismatch at {cells} cells",
        )

    timeout = [
        row
        for row in read_tsv(scaling / "measurements.tsv")
        if row["size_cells"] == "1024"
        and row["mode"] == "direct"
        and row["phase"] == "elaboration"
    ]
    require(len(timeout) == 1, "missing unique Direct 1024 timeout row")
    require(
        timeout[0]["status"] == "timeout"
        and timeout[0]["exit_status"] == "124"
        and decimal_seconds(
            timeout[0]["wall_seconds"], "Direct 1024 timeout"
        )
        == Decimal("600.030000")
        and timeout[0]["max_rss_kib"] == "",
        "Direct 1024 timeout normalization mismatch",
    )
    original_events = (
        root
        / "benchmarks/results/linux-canonical-scaling-20261127T064628Z"
        / "cgroups/020-elaboration-direct1024.events"
    )
    require(original_events.is_file(), "missing Direct 1024 cgroup events")
    require(
        "oom_kill 0" in original_events.read_text(encoding="utf-8"),
        "Direct 1024 recorded an unexpected OOM kill",
    )
    accounting = read_json(scaling / "cgroups/020-systemd-accounting.json")
    require(
        isinstance(accounting, dict)
        and accounting.get("CPU_USAGE_NSEC") == "601093878000",
        "Direct 1024 cgroup CPU accounting mismatch",
    )

    run_command = [
        "bash",
        str(root / "benchmarks/linux/render_plot.sh"),
        "--check",
        str(scaling.relative_to(root)),
    ]
    rendered = subprocess.run(
        run_command,
        cwd=root,
        text=True,
        capture_output=True,
        check=False,
    )
    require(
        rendered.returncode == 0,
        "Linux plot/table check failed: "
        + (rendered.stderr.strip() or rendered.stdout.strip() or "unknown error"),
    )

    upgraded = root / LINUX_UPGRADED
    require(
        "derived presentation of the first raw gate"
        in (upgraded / "README.txt").read_text(encoding="utf-8"),
        "upgraded Linux summary must identify its derived provenance",
    )
    require(
        "overall_status\tpass" in (upgraded / "overall_status.tsv").read_text()
        and "aggregate_prefix\texit_139_known"
        in (upgraded / "aggregate_prefix_status.tsv").read_text(),
        "upgraded Linux summary status mismatch",
    )
    verify_sha256_manifest(root, upgraded / "input.sha256")
    upgraded_rows = read_tsv(upgraded / "measurements.tsv")
    default_builds = [
        row
        for row in upgraded_rows
        if row["phase"] == "default_build" and row["mode"] == "Overlap"
    ]
    require(
        len(default_builds) == 1
        and default_builds[0]["status"] == "pass"
        and decimal_seconds(
            default_builds[0]["wall_seconds"], "upgraded clean build"
        )
        == Decimal("62.800000")
        and default_builds[0]["max_rss_kib"] == "4273232",
        "upgraded clean build row mismatch",
    )
    named = {
        row["mode"]: row
        for row in upgraded_rows
        if row["phase"] == "leanchecker"
        and row["mode"] in LINUX_UPGRADED_MODULES
    }
    require(
        set(named) == LINUX_UPGRADED_MODULES
        and all(row["status"] == "pass" for row in named.values()),
        "upgraded named-module replay coverage mismatch",
    )
    replay_sum = summed_seconds_at_precision(
        (row["wall_seconds"] for row in named.values()),
        3,
        "upgraded named-module replay",
    )
    require(replay_sum == Decimal("116.210"), "upgraded replay sum mismatch")
    proof_replay_sum = summed_seconds_at_precision(
        (
            row["wall_seconds"]
            for module, row in named.items()
            if module != "Bench"
        ),
        3,
        "upgraded proof-module replay",
    )
    require(
        proof_replay_sum == Decimal("111.250"),
        "upgraded proof-module replay sum mismatch",
    )
    aggregate = [
        row
        for row in upgraded_rows
        if row["phase"] == "leanchecker"
        and row["mode"] not in LINUX_UPGRADED_MODULES
    ]
    require(
        len(aggregate) == 1
        and aggregate[0]["status"] == "tool_error"
        and aggregate[0]["exit_status"] == "139",
        "aggregate-prefix diagnostic mismatch",
    )
    axioms = (upgraded / "independent-signoff/axioms.txt").read_text()
    for declaration in (
        "Overlap.discrete_limsup_le_continuous",
        "Overlap.discrete_upper_bound",
        "Overlap.whiteBridge",
    ):
        require(
            f"'{declaration}' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]" in axioms,
            f"axiom signature missing: {declaration}",
        )
    require(
        "Exit status: 139"
        in (root / "paper/validation/root-aggregate-139.txt").read_text(),
        "aggregate-prefix diagnostic note mismatch",
    )
    fresh = root / LINUX_FRESH
    fresh_time = (fresh / "time.log").read_text(encoding="utf-8")
    require(
        (fresh / "status.txt").read_text().strip() == "0"
        and (fresh / "output.log").read_bytes() == b""
        and "Elapsed (wall clock) time (h:mm:ss or m:ss): 8:48.84"
        in fresh_time
        and "Maximum resident set size (kbytes): 4041076" in fresh_time
        and "Exit status: 0" in fresh_time,
        "fresh aggregate-prefix replay mismatch",
    )
    require(
        (upgraded / "fresh-overlap/time.log").read_bytes()
        == (fresh / "time.log").read_bytes()
        and (upgraded / "fresh-overlap/status.txt").read_bytes()
        == (fresh / "status.txt").read_bytes(),
        "copied fresh-replay evidence differs from raw source",
    )

    confirmed = root / LINUX_CONFIRMED
    require(
        "overall_status\tpass"
        in (confirmed / "overall_status.tsv").read_text(encoding="utf-8")
        and "aggregate_prefix\ttool_error"
        in (confirmed / "aggregate_prefix_status.tsv").read_text(encoding="utf-8"),
        "confirmed module gate status mismatch",
    )
    verify_sha256_manifest(root, confirmed / "input.sha256")
    confirmed_rows = read_tsv(confirmed / "measurements.tsv")
    confirmed_build = [
        row
        for row in confirmed_rows
        if row["phase"] == "default_build" and row["mode"] == "Overlap"
    ]
    require(
        len(confirmed_build) == 1
        and confirmed_build[0]["status"] == "pass"
        and decimal_seconds(
            confirmed_build[0]["wall_seconds"], "confirmed clean build"
        )
        == Decimal("66.030000"),
        "confirmed clean build mismatch",
    )
    confirmed_named = [
        row
        for row in confirmed_rows
        if row["phase"] == "leanchecker"
        and row["mode"] in LINUX_UPGRADED_MODULES
        and row["status"] == "pass"
    ]
    require(
        len(confirmed_named) == len(LINUX_UPGRADED_MODULES),
        "confirmed named-module replay coverage mismatch",
    )
    confirmed_axioms = [
        row
        for row in confirmed_rows
        if row["phase"] == "axioms" and row["mode"] == "paper_axioms"
    ]
    require(
        len(confirmed_axioms) == 1 and confirmed_axioms[0]["status"] == "pass",
        "confirmed axiom probe mismatch",
    )

    matched = root / LINUX_MATCHED
    matched_rows = read_tsv(matched / "measurements.tsv")
    matched_build = [
        row
        for row in matched_rows
        if row["phase"] == "default_build" and row["mode"] == "Overlap"
    ]
    require(
        len(matched_build) == 1
        and matched_build[0]["status"] == "pass"
        and decimal_seconds(
            matched_build[0]["wall_seconds"], "matched v1 clean build"
        )
        == Decimal("52.240000"),
        "matched v1 clean build mismatch",
    )
    matched_replays = {
        row["mode"]: row
        for row in matched_rows
        if row["phase"] == "leanchecker" and row["mode"] in LINUX_CORE_REPLAYS
    }
    require(
        set(matched_replays) == set(LINUX_CORE_REPLAYS)
        and all(row["status"] == "pass" for row in matched_replays.values()),
        "matched v1 core replay mismatch",
    )
    matched_sum = summed_seconds_at_precision(
        (row["wall_seconds"] for row in matched_replays.values()),
        3,
        "matched v1 core replay",
    )
    require(matched_sum == Decimal("68.290"), "matched v1 replay sum mismatch")
    bench = [
        row
        for row in matched_rows
        if row["phase"] == "leanchecker" and row["mode"] == "Bench"
    ]
    require(
        len(bench) == 1
        and bench[0]["status"] == "pass"
        and decimal_seconds(bench[0]["wall_seconds"], "matched v1 Bench replay")
        == Decimal("5.400000"),
        "matched v1 Bench replay mismatch",
    )

    apple_rows = [
        json.loads(line, parse_float=Decimal)
        for line in (root / "benchmarks/results/20261127T033045Z/measurements.jsonl")
        .read_text(encoding="utf-8")
        .splitlines()
        if line.strip()
    ]
    apple_replay_seconds = [
        row["wall_seconds"]
        for row in apple_rows
        if row.get("phase") == "leanchecker"
        and row.get("unit") in LINUX_CORE_REPLAYS
    ]
    require(
        len(apple_replay_seconds) == len(LINUX_CORE_REPLAYS)
        and summed_seconds_at_precision(
            apple_replay_seconds, 6, "archived Apple core replay"
        )
        == Decimal("91.535958"),
        "archived Apple replay sum mismatch",
    )

    derived_upgrade = {
        row["scope"]: row
        for row in read_tsv(root / "paper/validation/linux-upgraded-gate.tsv")
    }
    require(
        derived_upgrade["clean_default_build"]["wall_seconds"] == "62.800"
        and derived_upgrade["named_module_replays"]["commands"] == "16"
        and derived_upgrade["named_module_replays"]["wall_seconds"] == "116.210"
        and derived_upgrade["aggregate_prefix_diagnostic"]["status"]
        == "diagnostic_failure"
        and derived_upgrade["fresh_aggregate_prefix"]["status"] == "pass"
        and derived_upgrade["fresh_aggregate_prefix"]["wall_seconds"] == "528.840",
        "derived upgraded Linux table mismatch",
    )
    derived_match = {
        row["platform"]: row
        for row in read_tsv(root / "paper/validation/linux-matched-witness.tsv")
    }
    require(
        derived_match["Linux AMD EPYC 7513"]["clean_build_seconds"]
        == "52.240000"
        and derived_match["Linux AMD EPYC 7513"]["eight_core_replays_seconds"]
        == "68.290000"
        and derived_match["Apple M3 Pro archived"]["eight_core_replays_seconds"]
        == "91.535958",
        "derived matched Linux table mismatch",
    )
    derived_confirmed = {
        row["scope"]: row
        for row in read_tsv(root / "paper/validation/linux-confirmed-gate.tsv")
    }
    require(
        derived_confirmed["clean_default_build"]["wall_seconds"] == "66.030"
        and derived_confirmed["named_module_replays"]["commands"] == "16"
        and derived_confirmed["named_module_replays"]["wall_seconds"] == "98.890"
        and derived_confirmed["expanded_axiom_probe"]["status"] == "pass"
        and derived_confirmed["aggregate_prefix_diagnostic"]["exit_status"]
        == "139"
        and derived_confirmed["runner_overall"]["status"] == "pass",
        "derived confirmed Linux table mismatch",
    )
    platform_table = (root / "paper/figures/platforms.tex").read_text(
        encoding="utf-8"
    )
    for expected_line in (
        r"v1.0.0 & M3 Pro & 29.24 & 3.53 & 8 & 91.54",
        r"v1.0.0 & EPYC   & 52.24 & 4.08 & 8 & 68.29",
        r"Current & EPYC  & 62.80 & 4.08 & 15 & 111.25",
    ):
        require(
            expected_line in platform_table,
            f"platform table row mismatch: {expected_line}",
        )


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
        validate_linux_artifacts(root)
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
