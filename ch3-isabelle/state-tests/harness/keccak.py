"""Minimal Keccak-256 and RLP helpers used by the state-test driver.

The test runner environment does not install eth-hash/pycryptodome, so the
driver keeps the small primitives needed to derive a contract address.
"""

from __future__ import annotations

MASK64 = (1 << 64) - 1

_ROT = (
    (0, 36, 3, 41, 18),
    (1, 44, 10, 45, 2),
    (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56),
    (27, 20, 39, 8, 14),
)

_RC = (
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
)


def _rotl(value: int, count: int) -> int:
    count %= 64
    return ((value << count) | (value >> (64 - count))) & MASK64


def _keccak_f(a):
    for rc in _RC:
        c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rotl(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                a[x][y] ^= d[x]

        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                b[y][(2 * x + 3 * y) % 5] = _rotl(a[x][y], _ROT[x][y])

        for x in range(5):
            for y in range(5):
                a[x][y] = b[x][y] ^ ((~b[(x + 1) % 5][y]) & b[(x + 2) % 5][y])

        a[0][0] ^= rc
    return a


def keccak256(data: bytes) -> bytes:
    rate = 136
    output_len = 32
    padded = bytearray(data)
    padded.append(0x01)
    while len(padded) % rate != rate - 1:
        padded.append(0x00)
    padded.append(0x80)

    state = [[0] * 5 for _ in range(5)]
    for block_start in range(0, len(padded), rate):
        block = padded[block_start:block_start + rate]
        for i in range(rate // 8):
            lane = int.from_bytes(block[i * 8:i * 8 + 8], "little")
            state[i % 5][i // 5] ^= lane
        state = _keccak_f(state)

    out = bytearray()
    while len(out) < output_len:
        for i in range(rate // 8):
            out.extend(state[i % 5][i // 5].to_bytes(8, "little"))
            if len(out) >= output_len:
                break
        if len(out) < output_len:
            state = _keccak_f(state)
    return bytes(out[:output_len])


def _rlp_length(length: int, offset: int) -> bytes:
    if length < 56:
        return bytes([offset + length])
    encoded = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(encoded)]) + encoded


def _rlp_bytes(value: bytes) -> bytes:
    if len(value) == 1 and value[0] < 0x80:
        return value
    return _rlp_length(len(value), 0x80) + value


def _rlp_int(value: int) -> bytes:
    if value == 0:
        return b"\x80"
    return _rlp_bytes(value.to_bytes((value.bit_length() + 7) // 8, "big"))


def rlp_encode(value) -> bytes:
    if isinstance(value, int):
        return _rlp_int(value)
    if isinstance(value, (bytes, bytearray)):
        return _rlp_bytes(bytes(value))
    if isinstance(value, (list, tuple)):
        payload = b"".join(rlp_encode(item) for item in value)
        return _rlp_length(len(payload), 0xC0) + payload
    raise TypeError(f"unsupported RLP value: {type(value)!r}")


def contract_address(sender_hex: str, nonce: int) -> str:
    sender_hex_body = sender_hex[2:] if sender_hex.startswith("0x") else sender_hex
    sender = bytes.fromhex(sender_hex_body)
    digest = keccak256(rlp_encode([sender, nonce]))
    return "0x" + digest[-20:].hex()