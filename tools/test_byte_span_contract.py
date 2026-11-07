#!/usr/bin/env python3
"""Offline algebra for docs/byte-span-api-specification.md; NOT runtime evidence.

Python bytes slicing copies: this model establishes no view lifetime/allocation,
Fibril typing, fuel charging, source construction or protocol/parser behavior.
The inspection count is a contract number, not measured evaluator work. No
production implementation is invoked or independently validated by these tests.
"""

import unittest
from typing import NamedTuple


class SpanObservation(NamedTuple):
    tag: str
    prefix: bytes
    rest: bytes
    inspections: int


def split32_model(data: bytes) -> tuple[bytes, bytes]:
    return data[:32], data[32:]


def span_set_model(bits: bytes, data: bytes) -> SpanObservation:
    if len(bits) != 32:
        return SpanObservation("MalformedClass", b"", data, 0)
    for index, byte in enumerate(data):
        if not ((bits[byte // 8] >> (byte % 8)) & 1):
            return SpanObservation("Spanned", data[:index], data[index:], index + 1)
    return SpanObservation("Spanned", data, b"", len(data))


def set_model(members: set[int]) -> bytes:
    """Model fixture encoding; NOT an available Fibril class constructor."""
    result = bytearray(32)
    for byte in members:
        result[byte // 8] |= 1 << (byte % 8)
    return bytes(result)


class ByteSpanContractModel(unittest.TestCase):
    def test_split32_conservation_and_progress(self):
        for length in (0, 1, 7, 31, 32, 33, 63, 64, 65, 4095, 4096, 4097):
            data = bytes(index % 256 for index in range(length))
            prefix, rest = split32_model(data)
            self.assertEqual(prefix + rest, data)
            self.assertEqual(len(prefix), min(32, length))
            self.assertEqual(bool(prefix), bool(data))
        # Iterating the model is algebra only, not primIterateBinary execution.
        rest = bytes(range(256)) * 16 + b"x"
        saved = rest
        pieces = []
        while rest:
            prefix, rest = split32_model(rest)
            pieces.append(prefix)
        self.assertEqual(len(pieces), 129)
        self.assertEqual(b"".join(pieces), saved)

    def test_all256_singletons_and_complements(self):
        universe = set(range(256))
        for member in range(256):
            singleton = set_model({member})
            complement = set_model(universe - {member})
            for byte in range(256):
                data = bytes([byte])
                for bits, matches in ((singleton, byte == member),
                                      (complement, byte != member)):
                    result = span_set_model(bits, data)
                    self.assertEqual(result.tag, "Spanned")
                    self.assertEqual(result.prefix, data if matches else b"")
                    self.assertEqual(result.rest, b"" if matches else data)
                    self.assertEqual(result.inspections, 1)

    def test_low_bit_first_boundaries(self):
        self.assertEqual(set_model({0, 7, 8, 127, 128, 255}),
                         bytes([0x81, 1] + [0] * 13 + [0x80, 1]
                               + [0] * 14 + [0x80]))

    def test_all_bitset_octet_values_are_valid(self):
        # Each possible octet in each table position; not all 2**256 sets.
        for position in range(32):
            for value in range(256):
                bits = bytearray(32)
                bits[position] = value
                result = span_set_model(bytes(bits), b"")
                self.assertEqual(result, SpanObservation("Spanned", b"", b"", 0))

    def test_invalid_lengths_preserve_input_without_inspection(self):
        data = b"\x00\xff\xc3(\x80unexamined"
        for length in (*range(32), 33, 255, 256, 257, 65536):
            result = span_set_model(bytes(length), data)
            self.assertEqual(result, SpanObservation("MalformedClass", b"", data, 0))

    def test_maximal_prefix_and_preserved_failing_byte_charge(self):
        bits = set_model({0, 97, 128, 255})
        for length in (0, 1, 31, 32, 33, 4095, 4096, 4097):
            matching = (b"\x00a\x80\xff" * (length // 4 + 1))[:length]
            for suffix in (b"", b"!", b"!\x00\xff"):
                data = matching + suffix
                result = span_set_model(bits, data)
                self.assertEqual(result.prefix, matching)
                self.assertEqual(result.rest, suffix)
                self.assertEqual(result.prefix + result.rest, data)
                self.assertEqual(result.inspections, length + bool(suffix))
                if suffix:
                    # The failing byte is inspected, preserved and charged again
                    # if the caller rescans it; not silently consumed or refunded.
                    repeated = span_set_model(bits, result.rest)
                    self.assertEqual(repeated.inspections, 1)
                    self.assertEqual(repeated.rest, suffix)

    def test_empty_and_full_sets(self):
        data = bytes(range(256))
        self.assertEqual(span_set_model(bytes(32), data),
                         SpanObservation("Spanned", b"", data, 1))
        self.assertEqual(span_set_model(b"\xff" * 32, data),
                         SpanObservation("Spanned", data, b"", 256))
        for bits in (bytes(32), b"\xff" * 32):
            self.assertEqual(span_set_model(bits, b""),
                             SpanObservation("Spanned", b"", b"", 0))


if __name__ == "__main__":
    unittest.main()
