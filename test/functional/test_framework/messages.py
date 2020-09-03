#!/usr/bin/env python3
# Copyright (c) 2010 ArtForz -- public domain half-a-node
# Copyright (c) 2012 Jeff Garzik
# Copyright (c) 2010-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Bitcoin test framework primitive and message structures

CBlock, CTransaction, CBlockHeader, CTxIn, CTxOut, etc....:
    data structures that should map to corresponding structures in
    bitcoin/primitives

msg_block, msg_tx, msg_headers, etc.:
    data structures that represent network messages

ser_*, deser_*: functions that handle serialization/deserialization.

Classes use __slots__ to ensure extraneous attributes aren't accidentally added
by tests, compromising their intended effect.
"""
from codecs import encode
import copy
import hashlib
from io import BytesIO
import random
import socket
import struct
import time
from typing import Optional, Union, List, Any, Callable, TypeVar

from test_framework.siphash import siphash256
from test_framework.util import hex_str_to_bytes, assert_equal

MIN_VERSION_SUPPORTED = 60001
MY_VERSION = 70016  # past wtxid relay
MY_SUBVERSION = b"/python-p2p-tester:0.0.3/"
MY_RELAY = 1 # from version 70001 onwards, fRelay should be appended to version messages (BIP37)

MAX_LOCATOR_SZ = 101
MAX_BLOCK_BASE_SIZE = 1000000
MAX_BLOOM_FILTER_SIZE = 36000
MAX_BLOOM_HASH_FUNCS = 50

COIN = 100000000  # 1 btc in satoshis
MAX_MONEY = 21000000 * COIN

BIP125_SEQUENCE_NUMBER = 0xfffffffd  # Sequence number that is BIP 125 opt-in and BIP 68-opt-out

MAX_PROTOCOL_MESSAGE_LENGTH = 4000000  # Maximum length of incoming protocol messages
MAX_HEADERS_RESULTS = 2000  # Number of headers sent in one getheaders result
MAX_INV_SIZE = 50000  # Maximum number of entries in an 'inv' protocol message

NODE_NETWORK = (1 << 0)
NODE_GETUTXO = (1 << 1)
NODE_BLOOM = (1 << 2)
NODE_WITNESS = (1 << 3)
NODE_COMPACT_FILTERS = (1 << 6)
NODE_NETWORK_LIMITED = (1 << 10)

MSG_TX = 1
MSG_BLOCK = 2
MSG_FILTERED_BLOCK = 3
MSG_CMPCT_BLOCK = 4
MSG_WTX = 5
MSG_WITNESS_FLAG = 1 << 30
MSG_TYPE_MASK = 0xffffffff >> 2
MSG_WITNESS_TX = MSG_TX | MSG_WITNESS_FLAG

FILTER_TYPE_BASIC = 0

CObject_TV = TypeVar('CObject_TV', 'CBlock', 'CTransaction', 'CBlockHeader',
                     'CTxIn', 'CTxOut', 'CAddress', 'CBlockLocator', 'CInv',
                     'COutPoint', 'CTxInWitness', 'CTxWitness',
                     'PrefilledTransaction', 'P2PHeaderAndShortIDs',
                     'P2PHeaderAndShortWitnessIDs', 'BlockTransactionsRequest',
                     'BlockTransactions', 'CPartialMerkleTree', 'CMerkleBlock')

# Serialization/deserialization tools
def sha256(s: bytes) -> bytes:
    return hashlib.new('sha256', s).digest()

def hash256(s: bytes) -> bytes:
    return sha256(sha256(s))

def ser_compact_size(l: int) -> bytes:
    r = b""
    if l < 253:
        r = struct.pack("B", l)
    elif l < 0x10000:
        r = struct.pack("<BH", 253, l)
    elif l < 0x100000000:
        r = struct.pack("<BI", 254, l)
    else:
        r = struct.pack("<BQ", 255, l)
    return r

def deser_compact_size(f: BytesIO) -> int:
    nit: int = struct.unpack("<B", f.read(1))[0]
    if nit == 253:
        nit = struct.unpack("<H", f.read(2))[0]
    elif nit == 254:
        nit = struct.unpack("<I", f.read(4))[0]
    elif nit == 255:
        nit = struct.unpack("<Q", f.read(8))[0]
    return nit

def deser_string(f: BytesIO) -> bytes:
    nit = deser_compact_size(f)
    return f.read(nit)

def ser_string(s: bytes) -> bytes:
    return ser_compact_size(len(s)) + s

def deser_uint256(f: BytesIO) -> int:
    r = 0
    for i in range(8):
        t = struct.unpack("<I", f.read(4))[0]
        r += t << (i * 32)
    return r


def ser_uint256(u: int) -> bytes:
    rs = b""
    for _ in range(8):
        rs += struct.pack("<I", u & 0xFFFFFFFF)
        u >>= 32
    return rs


def uint256_from_str(s: bytes) -> int:
    r = 0
    t = struct.unpack("<IIIIIIII", s[:32])
    for i in range(8):
        r += t[i] << (i * 32)
    return r


def uint256_from_compact(c: int) -> int:
    nbytes = (c >> 24) & 0xFF
    v = (c & 0xFFFFFF) << (8 * (nbytes - 3))
    return v


def deser_vector(f: BytesIO, c: Callable[[], CObject_TV]) -> List[CObject_TV]:
    nit = deser_compact_size(f)
    r = []
    for _ in range(nit):
        t = c()
        t.deserialize(f)
        r.append(t)
    return r


# ser_function_name: Allow for an alternate serialization function on the
# entries in the vector (we use this for serializing the vector of transactions
# for a witness block).
def ser_vector(l: List[Any], ser_function_name: Optional[str] = None) -> bytes:
    r = ser_compact_size(len(l))
    for i in l:
        if ser_function_name:
            r += getattr(i, ser_function_name)()
        else:
            r += i.serialize()
    return r


def deser_uint256_vector(f: BytesIO) -> List[int]:
    nit = deser_compact_size(f)
    r = []
    for _ in range(nit):
        t = deser_uint256(f)
        r.append(t)
    return r


def ser_uint256_vector(l: List[int]) -> bytes:
    r = ser_compact_size(len(l))
    for i in l:
        r += ser_uint256(i)
    return r


def deser_string_vector(f: BytesIO) -> List[bytes]:
    nit = deser_compact_size(f)
    r = []
    for _ in range(nit):
        t = deser_string(f)
        r.append(t)
    return r


def ser_string_vector(l: List[bytes]) -> bytes:
    r = ser_compact_size(len(l))
    for sv in l:
        r += ser_string(sv)
    return r


# Deserialize from a hex string representation (eg from RPC)
def FromHex(obj: CObject_TV, hex_string: bytes) -> CObject_TV:
    obj.deserialize(BytesIO(hex_str_to_bytes(hex_string)))
    return obj

# Convert a binary-serializable object to hex (eg for submission via RPC)
def ToHex(obj: CObject_TV) -> str:
    return obj.serialize().hex()

# Objects that map to bitcoind objects, which can be serialized/deserialized


class CAddress:
    __slots__ = ("ip", "nServices", "pchReserved", "port", "time")

    def __init__(self) -> None:
        self.time: int = 0
        self.nServices: int = 1
        self.pchReserved: bytes = b"\x00" * 10 + b"\xff" * 2
        self.ip: str = "0.0.0.0"
        self.port: int = 0

    def deserialize(self, f: BytesIO, *, with_time: bool = True) -> None:
        if with_time:
            # VERSION messages serialize CAddress objects without time
            self.time = struct.unpack("<i", f.read(4))[0]
        self.nServices = struct.unpack("<Q", f.read(8))[0]
        self.pchReserved = f.read(12)
        self.ip = socket.inet_ntoa(f.read(4))
        self.port = struct.unpack(">H", f.read(2))[0]

    def serialize(self, *, with_time: bool = True) -> bytes:
        r = b""
        if with_time:
            # VERSION messages serialize CAddress objects without time
            r += struct.pack("<i", self.time)
        r += struct.pack("<Q", self.nServices)
        r += self.pchReserved
        r += socket.inet_aton(self.ip)
        r += struct.pack(">H", self.port)
        return r

    def __repr__(self) -> str:
        return "CAddress(nServices=%i ip=%s port=%i)" % (self.nServices,
                                                         self.ip, self.port)


class CInv:
    __slots__ = ("hash", "type")

    typemap = {
        0: "Error",
        MSG_TX: "TX",
        MSG_BLOCK: "Block",
        MSG_TX | MSG_WITNESS_FLAG: "WitnessTx",
        MSG_BLOCK | MSG_WITNESS_FLAG: "WitnessBlock",
        MSG_FILTERED_BLOCK: "filtered Block",
        MSG_CMPCT_BLOCK: "CompactBlock",
        MSG_WTX: "WTX",
    }

    def __init__(self, t: int = 0, h: int = 0) -> None:
        self.type: int = t
        self.hash: int = h

    def deserialize(self, f: BytesIO) -> None:
        self.type = struct.unpack("<I", f.read(4))[0]
        self.hash = deser_uint256(f)

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<I", self.type)
        r += ser_uint256(self.hash)
        return r

    def __repr__(self) -> str:
        return "CInv(type=%s hash=%064x)" \
            % (self.typemap[self.type], self.hash)

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, CInv) and self.hash == other.hash and self.type == other.type


class CBlockLocator:
    __slots__ = ("nVersion", "vHave")

    def __init__(self) -> None:
        self.nVersion: int = MY_VERSION
        self.vHave: List[int] = []

    def deserialize(self, f: BytesIO) -> None:
        self.nVersion = struct.unpack("<i", f.read(4))[0]
        self.vHave = deser_uint256_vector(f)

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<i", self.nVersion)
        r += ser_uint256_vector(self.vHave)
        return r

    def __repr__(self) -> str:
        return "CBlockLocator(nVersion=%i vHave=%s)" \
            % (self.nVersion, repr(self.vHave))


class COutPoint:
    __slots__ = ("hash", "n")

    def __init__(self, hash: int = 0, n: int = 0) -> None:
        self.hash: int = hash
        self.n: int = n

    def deserialize(self, f: BytesIO) -> None:
        self.hash = deser_uint256(f)
        self.n = struct.unpack("<I", f.read(4))[0]

    def serialize(self) -> bytes:
        r = b""
        r += ser_uint256(self.hash)
        r += struct.pack("<I", self.n)
        return r

    def __repr__(self) -> str:
        return "COutPoint(hash=%064x n=%i)" % (self.hash, self.n)


class CTxIn:
    __slots__ = ("nSequence", "prevout", "scriptSig")

    def __init__(self,
                 outpoint: Optional[COutPoint] = None,
                 scriptSig: bytes = b"",
                 nSequence: int = 0
                 ) -> None:
        if outpoint is None:
            self.prevout = COutPoint()
        else:
            self.prevout = outpoint
        self.scriptSig: bytes = scriptSig
        self.nSequence: int = nSequence

    def deserialize(self, f: BytesIO) -> None:
        self.prevout = COutPoint()
        self.prevout.deserialize(f)
        self.scriptSig = deser_string(f)
        self.nSequence = struct.unpack("<I", f.read(4))[0]

    def serialize(self) -> bytes:
        r = b""
        r += self.prevout.serialize()
        r += ser_string(self.scriptSig)
        r += struct.pack("<I", self.nSequence)
        return r

    def __repr__(self) -> str:
        return "CTxIn(prevout=%s scriptSig=%s nSequence=%i)" \
            % (repr(self.prevout), self.scriptSig.hex(),
               self.nSequence)


class CTxOut:
    __slots__ = ("nValue", "scriptPubKey")

    def __init__(self, nValue: int = 0, scriptPubKey: bytes = b"") -> None:
        self.nValue: int = nValue
        self.scriptPubKey: bytes = scriptPubKey

    def deserialize(self, f: BytesIO) -> None:
        self.nValue = struct.unpack("<q", f.read(8))[0]
        self.scriptPubKey = deser_string(f)

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<q", self.nValue)
        r += ser_string(self.scriptPubKey)
        return r

    def __repr__(self) -> str:
        return "CTxOut(nValue=%i.%08i scriptPubKey=%s)" \
            % (self.nValue // COIN, self.nValue % COIN,
               self.scriptPubKey.hex())


class CScriptWitness:
    __slots__ = ("stack",)

    def __init__(self) -> None:
        # stack is a vector of strings
        self.stack: List[bytes] = []

    def __repr__(self) -> str:
        return "CScriptWitness(%s)" % \
               (",".join([x.hex() for x in self.stack]))

    def is_null(self) -> bool:
        if self.stack:
            return False
        return True


class CTxInWitness:
    __slots__ = ("scriptWitness",)

    def __init__(self) -> None:
        self.scriptWitness: CScriptWitness = CScriptWitness()

    def deserialize(self, f: BytesIO) -> None:
        self.scriptWitness.stack = deser_string_vector(f)

    def serialize(self) -> bytes:
        return ser_string_vector(self.scriptWitness.stack)

    def __repr__(self) -> str:
        return repr(self.scriptWitness)

    def is_null(self) -> bool:
        return self.scriptWitness.is_null()


class CTxWitness:
    __slots__ = ("vtxinwit",)

    def __init__(self) -> None:
        self.vtxinwit: List[CTxInWitness] = []

    def deserialize(self, f: BytesIO) -> None:
        for i in range(len(self.vtxinwit)):
            self.vtxinwit[i].deserialize(f)

    def serialize(self) -> bytes:
        r = b""
        # This is different than the usual vector serialization --
        # we omit the length of the vector, which is required to be
        # the same length as the transaction's vin vector.
        for x in self.vtxinwit:
            r += x.serialize()
        return r

    def __repr__(self) -> str:
        return "CTxWitness(%s)" % \
               (';'.join([repr(x) for x in self.vtxinwit]))

    def is_null(self) -> bool:
        for x in self.vtxinwit:
            if not x.is_null():
                return False
        return True


class CTransaction:
    __slots__ = ("hash", "nLockTime", "nVersion", "sha256", "vin", "vout",
                 "wit")

    def __init__(self, tx: Optional['CTransaction'] = None) -> None:
        if tx is None:
            self.nVersion: int = 1
            self.vin: List[CTxIn] = []
            self.vout: List[CTxOut] = []
            self.wit: CTxWitness = CTxWitness()
            self.nLockTime: int = 0
            self.sha256: Optional[int] = None
            self.hash: Optional[str] = None
        else:
            self.nVersion = tx.nVersion
            self.vin = copy.deepcopy(tx.vin)
            self.vout = copy.deepcopy(tx.vout)
            self.nLockTime = tx.nLockTime
            self.sha256 = tx.sha256
            self.hash = tx.hash
            self.wit = copy.deepcopy(tx.wit)

    def deserialize(self, f: BytesIO) -> None:
        self.nVersion = struct.unpack("<i", f.read(4))[0]
        self.vin = deser_vector(f, CTxIn)
        flags = 0
        if len(self.vin) == 0:
            flags = struct.unpack("<B", f.read(1))[0]
            # Not sure why flags can't be zero, but this
            # matches the implementation in bitcoind
            if (flags != 0):
                self.vin = deser_vector(f, CTxIn)
                self.vout = deser_vector(f, CTxOut)
        else:
            self.vout = deser_vector(f, CTxOut)
        if flags != 0:
            self.wit.vtxinwit = [CTxInWitness() for _ in range(len(self.vin))]
            self.wit.deserialize(f)
        else:
            self.wit = CTxWitness()
        self.nLockTime = struct.unpack("<I", f.read(4))[0]
        self.sha256 = None
        self.hash = None

    def serialize_without_witness(self) -> bytes:
        r = b""
        r += struct.pack("<i", self.nVersion)
        r += ser_vector(self.vin)
        r += ser_vector(self.vout)
        r += struct.pack("<I", self.nLockTime)
        return r

    # Only serialize with witness when explicitly called for
    def serialize_with_witness(self) -> bytes:
        flags = 0
        if not self.wit.is_null():
            flags |= 1
        r = b""
        r += struct.pack("<i", self.nVersion)
        if flags:
            r += ser_vector([])
            r += struct.pack("<B", flags)
        r += ser_vector(self.vin)
        r += ser_vector(self.vout)
        if flags & 1:
            if (len(self.wit.vtxinwit) != len(self.vin)):
                # vtxinwit must have the same length as vin
                self.wit.vtxinwit = self.wit.vtxinwit[:len(self.vin)]
                for _ in range(len(self.wit.vtxinwit), len(self.vin)):
                    self.wit.vtxinwit.append(CTxInWitness())
            r += self.wit.serialize()
        r += struct.pack("<I", self.nLockTime)
        return r

    # Regular serialization is with witness -- must explicitly
    # call serialize_without_witness to exclude witness data.
    def serialize(self) -> bytes:
        return self.serialize_with_witness()

    # Recalculate the txid (transaction hash without witness)
    def rehash(self) -> str:
        self.sha256 = None
        self.calc_sha256()
        assert self.hash is not None
        return self.hash

    # We will only cache the serialization without witness in
    # self.sha256 and self.hash -- those are expected to be the txid.
    def calc_sha256(self, with_witness: bool = False) -> int:
        if with_witness:
            # Don't cache the result, just return it
            return uint256_from_str(hash256(self.serialize_with_witness()))

        if self.sha256 is None:
            self.sha256 = uint256_from_str(hash256(self.serialize_without_witness()))
        self.hash = encode(hash256(self.serialize_without_witness())[::-1], 'hex_codec').decode('ascii')
        return self.sha256

    def is_valid(self) -> bool:
        self.calc_sha256()
        for tout in self.vout:
            if tout.nValue < 0 or tout.nValue > 21000000 * COIN:
                return False
        return True

    def __repr__(self) -> str:
        return "CTransaction(nVersion=%i vin=%s vout=%s wit=%s nLockTime=%i)" \
            % (self.nVersion, repr(self.vin), repr(self.vout), repr(self.wit), self.nLockTime)


class CBlockHeader:
    __slots__ = ("hash", "hashMerkleRoot", "hashPrevBlock", "nBits", "nNonce",
                 "nTime", "nVersion", "sha256")

    def __init__(self, header: Optional['CBlockHeader'] = None) -> None:
        if header is None:
            self.set_null()
        else:
            self.nVersion: int = header.nVersion
            self.hashPrevBlock: int = header.hashPrevBlock
            self.hashMerkleRoot: int = header.hashMerkleRoot
            self.nTime: int = header.nTime
            self.nBits: int = header.nBits
            self.nNonce: int = header.nNonce
            self.sha256: Optional[int] = header.sha256
            self.hash: Optional[str] = header.hash
            self.calc_sha256()

    def set_null(self) -> None:
        self.nVersion = 1
        self.hashPrevBlock = 0
        self.hashMerkleRoot = 0
        self.nTime = 0
        self.nBits = 0
        self.nNonce = 0
        self.sha256 = None
        self.hash = None

    def deserialize(self, f: BytesIO) -> None:
        self.nVersion = struct.unpack("<i", f.read(4))[0]
        self.hashPrevBlock = deser_uint256(f)
        self.hashMerkleRoot = deser_uint256(f)
        self.nTime = struct.unpack("<I", f.read(4))[0]
        self.nBits = struct.unpack("<I", f.read(4))[0]
        self.nNonce = struct.unpack("<I", f.read(4))[0]
        self.sha256 = None
        self.hash = None

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<i", self.nVersion)
        r += ser_uint256(self.hashPrevBlock)
        r += ser_uint256(self.hashMerkleRoot)
        r += struct.pack("<I", self.nTime)
        r += struct.pack("<I", self.nBits)
        r += struct.pack("<I", self.nNonce)
        return r

    def calc_sha256(self) -> None:
        if self.sha256 is None:
            r = b""
            r += struct.pack("<i", self.nVersion)
            r += ser_uint256(self.hashPrevBlock)
            r += ser_uint256(self.hashMerkleRoot)
            r += struct.pack("<I", self.nTime)
            r += struct.pack("<I", self.nBits)
            r += struct.pack("<I", self.nNonce)
            self.sha256 = uint256_from_str(hash256(r))
            self.hash = encode(hash256(r)[::-1], 'hex_codec').decode('ascii')

    def rehash(self) -> int:
        self.sha256 = None
        self.calc_sha256()
        assert self.sha256 is not None
        return self.sha256

    def __repr__(self) -> str:
        return "CBlockHeader(nVersion=%i hashPrevBlock=%064x hashMerkleRoot=%064x nTime=%s nBits=%08x nNonce=%08x)" \
            % (self.nVersion, self.hashPrevBlock, self.hashMerkleRoot,
               time.ctime(self.nTime), self.nBits, self.nNonce)

BLOCK_HEADER_SIZE = len(CBlockHeader().serialize())
assert_equal(BLOCK_HEADER_SIZE, 80)

class CBlock(CBlockHeader):
    __slots__ = ("vtx",)

    def __init__(self, header: Optional[CBlockHeader] = None) -> None:
        super().__init__(header)
        self.vtx: List[CTransaction] = []

    def deserialize(self, f: BytesIO) -> None:
        super().deserialize(f)
        self.vtx = deser_vector(f, CTransaction)

    def serialize(self, with_witness: bool = True) -> bytes:
        r = b""
        r += super().serialize()
        if with_witness:
            r += ser_vector(self.vtx, "serialize_with_witness")
        else:
            r += ser_vector(self.vtx, "serialize_without_witness")
        return r

    # Calculate the merkle root given a vector of transaction hashes
    @classmethod
    def get_merkle_root(cls, hashes: List[bytes]) -> int:
        while len(hashes) > 1:
            newhashes = []
            for i in range(0, len(hashes), 2):
                i2 = min(i+1, len(hashes)-1)
                newhashes.append(hash256(hashes[i] + hashes[i2]))
            hashes = newhashes
        return uint256_from_str(hashes[0])

    def calc_merkle_root(self) -> int:
        hashes = []
        for tx in self.vtx:
            tx.calc_sha256()
            assert tx.sha256 is not None
            hashes.append(ser_uint256(tx.sha256))
        return self.get_merkle_root(hashes)

    def calc_witness_merkle_root(self) -> int:
        # For witness root purposes, the hash of the
        # coinbase, with witness, is defined to be 0...0
        hashes = [ser_uint256(0)]

        for tx in self.vtx[1:]:
            # Calculate the hashes with witness data
            hashes.append(ser_uint256(tx.calc_sha256(True)))

        return self.get_merkle_root(hashes)

    def is_valid(self) -> bool:
        self.calc_sha256()
        assert self.sha256 is not None
        target = uint256_from_compact(self.nBits)
        if self.sha256 > target:
            return False
        for tx in self.vtx:
            if not tx.is_valid():
                return False
        if self.calc_merkle_root() != self.hashMerkleRoot:
            return False
        return True

    def solve(self) -> None:
        self.rehash()
        assert self.sha256 is not None
        target = uint256_from_compact(self.nBits)
        while self.sha256 > target:
            self.nNonce += 1
            self.rehash()

    def __repr__(self) -> str:
        return "CBlock(nVersion=%i hashPrevBlock=%064x hashMerkleRoot=%064x nTime=%s nBits=%08x nNonce=%08x vtx=%s)" \
            % (self.nVersion, self.hashPrevBlock, self.hashMerkleRoot,
               time.ctime(self.nTime), self.nBits, self.nNonce, repr(self.vtx))


class PrefilledTransaction:
    __slots__ = ("index", "tx")

    def __init__(self, index: int = 0, tx: Optional[CTransaction] = None) -> None:
        self.index = index
        self.tx = tx

    def deserialize(self, f: BytesIO) -> None:
        self.index = deser_compact_size(f)
        self.tx = CTransaction()
        self.tx.deserialize(f)

    def serialize(self, with_witness: bool = True) -> bytes:
        assert self.tx is not None
        r = b""
        r += ser_compact_size(self.index)
        if with_witness:
            r += self.tx.serialize_with_witness()
        else:
            r += self.tx.serialize_without_witness()
        return r

    def serialize_without_witness(self) -> bytes:
        return self.serialize(with_witness=False)

    def serialize_with_witness(self) -> bytes:
        return self.serialize(with_witness=True)

    def __repr__(self) -> str:
        return "PrefilledTransaction(index=%d, tx=%s)" % (self.index, repr(self.tx))


# This is what we send on the wire, in a cmpctblock message.
class P2PHeaderAndShortIDs:
    __slots__ = ("header", "nonce", "prefilled_txn", "prefilled_txn_length",
                 "shortids", "shortids_length")

    def __init__(self) -> None:
        self.header: CBlockHeader = CBlockHeader()
        self.nonce: int = 0
        self.shortids_length: int = 0
        self.shortids: List[int] = []
        self.prefilled_txn_length: int = 0
        self.prefilled_txn: List[PrefilledTransaction] = []

    def deserialize(self, f: BytesIO) -> None:
        self.header.deserialize(f)
        self.nonce = struct.unpack("<Q", f.read(8))[0]
        self.shortids_length = deser_compact_size(f)
        for _ in range(self.shortids_length):
            # shortids are defined to be 6 bytes in the spec, so append
            # two zero bytes and read it in as an 8-byte number
            self.shortids.append(struct.unpack("<Q", f.read(6) + b'\x00\x00')[0])
        self.prefilled_txn = deser_vector(f, PrefilledTransaction)
        self.prefilled_txn_length = len(self.prefilled_txn)

    # When using version 2 compact blocks, we must serialize with_witness.
    def serialize(self, with_witness: bool = False) -> bytes:
        r = b""
        r += self.header.serialize()
        r += struct.pack("<Q", self.nonce)
        r += ser_compact_size(self.shortids_length)
        for x in self.shortids:
            # We only want the first 6 bytes
            r += struct.pack("<Q", x)[0:6]
        if with_witness:
            r += ser_vector(self.prefilled_txn, "serialize_with_witness")
        else:
            r += ser_vector(self.prefilled_txn, "serialize_without_witness")
        return r

    def __repr__(self) -> str:
        return "P2PHeaderAndShortIDs(header=%s, nonce=%d, shortids_length=%d, shortids=%s, prefilled_txn_length=%d, prefilledtxn=%s" % (repr(self.header), self.nonce, self.shortids_length, repr(self.shortids), self.prefilled_txn_length, repr(self.prefilled_txn))


# P2P version of the above that will use witness serialization (for compact
# block version 2)
class P2PHeaderAndShortWitnessIDs(P2PHeaderAndShortIDs):
    __slots__ = ()

    def serialize(self, _: bool = False) -> bytes:
        return super().serialize(with_witness=True)

# Calculate the BIP 152-compact blocks shortid for a given transaction hash
def calculate_shortid(k0: int, k1: int, tx_hash: int) -> int:
    expected_shortid: int = siphash256(k0, k1, tx_hash)
    expected_shortid &= 0x0000ffffffffffff
    return expected_shortid


# This version gets rid of the array lengths, and reinterprets the differential
# encoding into indices that can be used for lookup.
class HeaderAndShortIDs:
    __slots__ = ("header", "nonce", "prefilled_txn", "shortids", "use_witness")

    def __init__(self, p2pheaders_and_shortids: Optional[P2PHeaderAndShortIDs] = None) -> None:
        self.header: CBlockHeader = CBlockHeader()
        self.nonce: int = 0
        self.shortids: List[int] = []
        self.prefilled_txn: List[PrefilledTransaction] = []
        self.use_witness: bool = False

        if p2pheaders_and_shortids is not None:
            self.header = p2pheaders_and_shortids.header
            self.nonce = p2pheaders_and_shortids.nonce
            self.shortids = p2pheaders_and_shortids.shortids
            last_index = -1
            for x in p2pheaders_and_shortids.prefilled_txn:
                self.prefilled_txn.append(PrefilledTransaction(x.index + last_index + 1, x.tx))
                last_index = self.prefilled_txn[-1].index

    def to_p2p(self) -> Union[P2PHeaderAndShortWitnessIDs, P2PHeaderAndShortIDs]:
        if self.use_witness:
            ret = P2PHeaderAndShortWitnessIDs()
        else:
            ret = P2PHeaderAndShortIDs()  # type: ignore    # https://github.com/python/mypy/issues/6233
        ret.header = self.header
        ret.nonce = self.nonce
        ret.shortids_length = len(self.shortids)
        ret.shortids = self.shortids
        ret.prefilled_txn_length = len(self.prefilled_txn)
        ret.prefilled_txn = []
        last_index = -1
        for x in self.prefilled_txn:
            ret.prefilled_txn.append(PrefilledTransaction(x.index - last_index - 1, x.tx))
            last_index = x.index
        return ret

    def get_siphash_keys(self) -> List[int]:
        header_nonce = self.header.serialize()
        header_nonce += struct.pack("<Q", self.nonce)
        hash_header_nonce_as_str = sha256(header_nonce)
        key0 = struct.unpack("<Q", hash_header_nonce_as_str[0:8])[0]
        key1 = struct.unpack("<Q", hash_header_nonce_as_str[8:16])[0]
        return [ key0, key1 ]

    # Version 2 compact blocks use wtxid in shortids (rather than txid)
    def initialize_from_block(self,
                              block: CBlock,
                              nonce: int = 0,
                              prefill_list: Optional[List[int]] = None,
                              use_witness: bool = False
                              ) -> None:
        if prefill_list is None:
            prefill_list = [0]
        self.header = CBlockHeader(block)
        self.nonce = nonce
        self.prefilled_txn = [ PrefilledTransaction(i, block.vtx[i]) for i in prefill_list ]
        self.shortids = []
        self.use_witness = use_witness
        [k0, k1] = self.get_siphash_keys()
        for i in range(len(block.vtx)):
            if i not in prefill_list:
                tx_hash = block.vtx[i].sha256
                if use_witness:
                    tx_hash = block.vtx[i].calc_sha256(with_witness=True)
                assert tx_hash is not None
                self.shortids.append(calculate_shortid(k0, k1, tx_hash))

    def __repr__(self) -> str:
        return "HeaderAndShortIDs(header=%s, nonce=%d, shortids=%s, prefilledtxn=%s" % (repr(self.header), self.nonce, repr(self.shortids), repr(self.prefilled_txn))


class BlockTransactionsRequest:
    __slots__ = ("blockhash", "indexes")

    def __init__(self, blockhash: int = 0, indexes: Optional[List[int]] = None) -> None:
        self.blockhash = blockhash
        self.indexes = indexes if indexes is not None else []

    def deserialize(self, f: BytesIO) -> None:
        self.blockhash = deser_uint256(f)
        indexes_length = deser_compact_size(f)
        for _ in range(indexes_length):
            self.indexes.append(deser_compact_size(f))

    def serialize(self) -> bytes:
        r = b""
        r += ser_uint256(self.blockhash)
        r += ser_compact_size(len(self.indexes))
        for x in self.indexes:
            r += ser_compact_size(x)
        return r

    # helper to set the differentially encoded indexes from absolute ones
    def from_absolute(self, absolute_indexes: List[int]) -> None:
        self.indexes = []
        last_index = -1
        for x in absolute_indexes:
            self.indexes.append(x-last_index-1)
            last_index = x

    def to_absolute(self) -> List[int]:
        absolute_indexes = []
        last_index = -1
        for x in self.indexes:
            absolute_indexes.append(x+last_index+1)
            last_index = absolute_indexes[-1]
        return absolute_indexes

    def __repr__(self) -> str:
        return "BlockTransactionsRequest(hash=%064x indexes=%s)" % (self.blockhash, repr(self.indexes))


class BlockTransactions:
    __slots__ = ("blockhash", "transactions")

    def __init__(self, blockhash: int = 0, transactions: Optional[List[CTransaction]] = None) -> None:
        self.blockhash: int = blockhash
        self.transactions: List[CTransaction] = transactions if transactions is not None else []

    def deserialize(self, f: BytesIO) -> None:
        self.blockhash = deser_uint256(f)
        self.transactions = deser_vector(f, CTransaction)

    def serialize(self, with_witness: bool = True) -> bytes:
        r = b""
        r += ser_uint256(self.blockhash)
        if with_witness:
            r += ser_vector(self.transactions, "serialize_with_witness")
        else:
            r += ser_vector(self.transactions, "serialize_without_witness")
        return r

    def __repr__(self) -> str:
        return "BlockTransactions(hash=%064x transactions=%s)" % (self.blockhash, repr(self.transactions))


class CPartialMerkleTree:
    __slots__ = ("nTransactions", "vBits", "vHash")

    def __init__(self) -> None:
        self.nTransactions: int = 0
        self.vHash: List[int] = []
        self.vBits: List[int] = []

    def deserialize(self, f: BytesIO) -> None:
        self.nTransactions = struct.unpack("<i", f.read(4))[0]
        self.vHash = deser_uint256_vector(f)
        vBytes = deser_string(f)
        self.vBits = []
        for i in range(len(vBytes) * 8):
            self.vBits.append(vBytes[i//8] & (1 << (i % 8)) != 0)

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<i", self.nTransactions)
        r += ser_uint256_vector(self.vHash)
        vBytesArray = bytearray([0x00] * ((len(self.vBits) + 7)//8))
        for i in range(len(self.vBits)):
            vBytesArray[i // 8] |= self.vBits[i] << (i % 8)
        r += ser_string(bytes(vBytesArray))
        return r

    def __repr__(self) -> str:
        return "CPartialMerkleTree(nTransactions=%d, vHash=%s, vBits=%s)" % (self.nTransactions, repr(self.vHash), repr(self.vBits))


class CMerkleBlock:
    __slots__ = ("header", "txn")

    def __init__(self) -> None:
        self.header: CBlockHeader = CBlockHeader()
        self.txn: CPartialMerkleTree = CPartialMerkleTree()

    def deserialize(self, f: BytesIO) -> None:
        self.header.deserialize(f)
        self.txn.deserialize(f)

    def serialize(self) -> bytes:
        r = b""
        r += self.header.serialize()
        r += self.txn.serialize()
        return r

    def __repr__(self) -> str:
        return "CMerkleBlock(header=%s, txn=%s)" % (repr(self.header), repr(self.txn))


# Objects that correspond to messages on the wire

class msg_version:
    __slots__ = ("addrFrom", "addrTo", "nNonce", "nRelay", "nServices",
                 "nStartingHeight", "nTime", "nVersion", "strSubVer")
    msgtype = b"version"

    def __init__(self) -> None:
        self.nVersion: int = MY_VERSION
        self.nServices: int = NODE_NETWORK | NODE_WITNESS
        self.nTime: int = int(time.time())
        self.addrTo: CAddress = CAddress()
        self.addrFrom: CAddress = CAddress()
        self.nNonce: int = random.getrandbits(64)
        self.strSubVer: bytes = MY_SUBVERSION
        self.nStartingHeight: int = -1
        self.nRelay: int = MY_RELAY

    def deserialize(self, f: BytesIO) -> None:
        self.nVersion = struct.unpack("<i", f.read(4))[0]
        self.nServices = struct.unpack("<Q", f.read(8))[0]
        self.nTime = struct.unpack("<q", f.read(8))[0]
        self.addrTo = CAddress()
        self.addrTo.deserialize(f, with_time=False)

        self.addrFrom = CAddress()
        self.addrFrom.deserialize(f, with_time=False)
        self.nNonce = struct.unpack("<Q", f.read(8))[0]
        self.strSubVer = deser_string(f)

        self.nStartingHeight = struct.unpack("<i", f.read(4))[0]

        if self.nVersion >= 70001:
            # Relay field is optional for version 70001 onwards
            try:
                self.nRelay = struct.unpack("<b", f.read(1))[0]
            except:
                self.nRelay = 0
        else:
            self.nRelay = 0

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<i", self.nVersion)
        r += struct.pack("<Q", self.nServices)
        r += struct.pack("<q", self.nTime)
        r += self.addrTo.serialize(with_time=False)
        r += self.addrFrom.serialize(with_time=False)
        r += struct.pack("<Q", self.nNonce)
        r += ser_string(self.strSubVer)
        r += struct.pack("<i", self.nStartingHeight)
        r += struct.pack("<b", self.nRelay)
        return r

    def __repr__(self) -> str:
        return 'msg_version(nVersion=%i nServices=%i nTime=%s addrTo=%s addrFrom=%s nNonce=0x%016X strSubVer=%r nStartingHeight=%i nRelay=%i)' \
            % (self.nVersion, self.nServices, time.ctime(self.nTime),
               repr(self.addrTo), repr(self.addrFrom), self.nNonce,
               self.strSubVer, self.nStartingHeight, self.nRelay)


class msg_verack:
    __slots__ = ()
    msgtype = b"verack"

    def __init__(self) -> None:
        pass

    def deserialize(self, f: BytesIO) -> None:
        pass

    def serialize(self) -> bytes:
        return b""

    def __repr__(self) -> str:
        return "msg_verack()"


class msg_addr:
    __slots__ = ("addrs",)
    msgtype = b"addr"

    def __init__(self) -> None:
        self.addrs: List[CAddress] = []

    def deserialize(self, f: BytesIO) -> None:
        self.addrs = deser_vector(f, CAddress)

    def serialize(self) -> bytes:
        return ser_vector(self.addrs)

    def __repr__(self) -> str:
        return "msg_addr(addrs=%s)" % (repr(self.addrs))


class msg_inv:
    __slots__ = ("inv",)
    msgtype = b"inv"

    def __init__(self, inv: Optional[List[CInv]] = None) -> None:
        if inv is None:
            self.inv = []
        else:
            self.inv = inv

    def deserialize(self, f: BytesIO) -> None:
        self.inv = deser_vector(f, CInv)

    def serialize(self) -> bytes:
        assert self.inv is not None
        return ser_vector(self.inv)

    def __repr__(self) -> str:
        return "msg_inv(inv=%s)" % (repr(self.inv))


class msg_getdata:
    __slots__ = ("inv",)
    msgtype = b"getdata"

    def __init__(self, inv: Optional[List[CInv]] = None) -> None:
        self.inv: List[CInv] = inv if inv is not None else []

    def deserialize(self, f: BytesIO) -> None:
        self.inv = deser_vector(f, CInv)

    def serialize(self) -> bytes:
        return ser_vector(self.inv)

    def __repr__(self) -> str:
        return "msg_getdata(inv=%s)" % (repr(self.inv))


class msg_getblocks:
    __slots__ = ("locator", "hashstop")
    msgtype = b"getblocks"

    def __init__(self) -> None:
        self.locator = CBlockLocator()
        self.hashstop = 0

    def deserialize(self, f: BytesIO) -> None:
        self.locator = CBlockLocator()
        self.locator.deserialize(f)
        self.hashstop = deser_uint256(f)

    def serialize(self) -> bytes:
        r = b""
        r += self.locator.serialize()
        r += ser_uint256(self.hashstop)
        return r

    def __repr__(self) -> str:
        return "msg_getblocks(locator=%s hashstop=%064x)" \
            % (repr(self.locator), self.hashstop)


class msg_tx:
    __slots__ = ("tx",)
    msgtype = b"tx"

    def __init__(self, tx: CTransaction = CTransaction()) -> None:
        self.tx = tx

    def deserialize(self, f: BytesIO) -> None:
        self.tx.deserialize(f)

    def serialize(self) -> bytes:
        return self.tx.serialize_with_witness()

    def __repr__(self) -> str:
        return "msg_tx(tx=%s)" % (repr(self.tx))


class msg_wtxidrelay:
    __slots__ = ()
    msgtype = b"wtxidrelay"

    def __init__(self) -> None:
        pass

    def deserialize(self, f: BytesIO) -> None:
        pass

    def serialize(self) -> bytes:
        return b""

    def __repr__(self) -> str:
        return "msg_wtxidrelay()"


class msg_no_witness_tx(msg_tx):
    __slots__ = ()

    def serialize(self) -> bytes:
        return self.tx.serialize_without_witness()


class msg_block:
    __slots__ = ("block",)
    msgtype = b"block"

    def __init__(self, block: Optional[CBlock] = None) -> None:
        if block is None:
            self.block = CBlock()
        else:
            self.block = block

    def deserialize(self, f: BytesIO) -> None:
        self.block.deserialize(f)

    def serialize(self) -> bytes:
        assert self.block is not None
        return self.block.serialize()

    def __repr__(self) -> str:
        return "msg_block(block=%s)" % (repr(self.block))


# for cases where a user needs tighter control over what is sent over the wire
# note that the user must supply the name of the msgtype, and the data
class msg_generic:
    __slots__ = ("msgtype", "data")

    def __init__(self, msgtype: str, data: Optional[bytes] = None) -> None:
        self.msgtype = msgtype
        self.data = data

    def serialize(self) -> bytes:
        assert self.data is not None
        return self.data

    def __repr__(self) -> str:
        return "msg_generic()"


class msg_no_witness_block(msg_block):
    __slots__ = ()

    def serialize(self) -> bytes:
        return self.block.serialize(with_witness=False)


class msg_getaddr:
    __slots__ = ()
    msgtype = b"getaddr"

    def __init__(self) -> None:
        pass

    def deserialize(self, f: BytesIO) -> None:
        pass

    def serialize(self) -> bytes:
        return b""

    def __repr__(self) -> str:
        return "msg_getaddr()"


class msg_ping:
    __slots__ = ("nonce",)
    msgtype = b"ping"

    def __init__(self, nonce: int = 0) -> None:
        self.nonce = nonce

    def deserialize(self, f: BytesIO) -> None:
        self.nonce = struct.unpack("<Q", f.read(8))[0]

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<Q", self.nonce)
        return r

    def __repr__(self) -> str:
        return "msg_ping(nonce=%08x)" % self.nonce


class msg_pong:
    __slots__ = ("nonce",)
    msgtype = b"pong"

    def __init__(self, nonce: int = 0) -> None:
        self.nonce = nonce

    def deserialize(self, f: BytesIO) -> None:
        self.nonce = struct.unpack("<Q", f.read(8))[0]

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<Q", self.nonce)
        return r

    def __repr__(self) -> str:
        return "msg_pong(nonce=%08x)" % self.nonce


class msg_mempool:
    __slots__ = ()
    msgtype = b"mempool"

    def __init__(self) -> None:
        pass

    def deserialize(self, f: BytesIO) -> None:
        pass

    def serialize(self) -> bytes:
        return b""

    def __repr__(self) -> str:
        return "msg_mempool()"


class msg_notfound:
    __slots__ = ("vec", )
    msgtype = b"notfound"

    def __init__(self, vec: Optional[List[CInv]] = None) -> None:
        self.vec = vec or []

    def deserialize(self, f: BytesIO) -> None:
        self.vec = deser_vector(f, CInv)

    def serialize(self) -> bytes:
        return ser_vector(self.vec)

    def __repr__(self) -> str:
        return "msg_notfound(vec=%s)" % (repr(self.vec))


class msg_sendheaders:
    __slots__ = ()
    msgtype = b"sendheaders"

    def __init__(self) -> None:
        pass

    def deserialize(self, f: BytesIO) -> None:
        pass

    def serialize(self) -> bytes:
        return b""

    def __repr__(self) -> str:
        return "msg_sendheaders()"


# getheaders message has
# number of entries
# vector of hashes
# hash_stop (hash of last desired block header, 0 to get as many as possible)
class msg_getheaders:
    __slots__ = ("hashstop", "locator",)
    msgtype = b"getheaders"

    def __init__(self) -> None:
        self.locator = CBlockLocator()
        self.hashstop = 0

    def deserialize(self, f: BytesIO) -> None:
        self.locator = CBlockLocator()
        self.locator.deserialize(f)
        self.hashstop = deser_uint256(f)

    def serialize(self) -> bytes:
        r = b""
        r += self.locator.serialize()
        r += ser_uint256(self.hashstop)
        return r

    def __repr__(self) -> str:
        return "msg_getheaders(locator=%s, stop=%064x)" \
            % (repr(self.locator), self.hashstop)


# headers message has
# <count> <vector of block headers>
class msg_headers:
    __slots__ = ("headers",)
    msgtype = b"headers"

    def __init__(self, headers: Optional[List[CBlockHeader]] = None) -> None:
        self.headers = headers if headers is not None else []

    def deserialize(self, f: BytesIO) -> None:
        # comment in bitcoind indicates these should be deserialized as blocks
        blocks = deser_vector(f, CBlock)
        for x in blocks:
            self.headers.append(CBlockHeader(x))

    def serialize(self) -> bytes:
        assert self.headers is not None
        blocks = [CBlock(x) for x in self.headers]
        return ser_vector(blocks)

    def __repr__(self) -> str:
        return "msg_headers(headers=%s)" % repr(self.headers)


class msg_merkleblock:
    __slots__ = ("merkleblock",)
    msgtype = b"merkleblock"

    def __init__(self, merkleblock: Optional[CMerkleBlock] = None) -> None:
        if merkleblock is None:
            self.merkleblock = CMerkleBlock()
        else:
            self.merkleblock = merkleblock

    def deserialize(self, f: BytesIO) -> None:
        self.merkleblock.deserialize(f)

    def serialize(self) -> bytes:
        assert self.merkleblock is not None
        return self.merkleblock.serialize()

    def __repr__(self) -> str:
        return "msg_merkleblock(merkleblock=%s)" % (repr(self.merkleblock))


class msg_filterload:
    __slots__ = ("data", "nHashFuncs", "nTweak", "nFlags")
    msgtype = b"filterload"

    def __init__(self,
                 data: bytes = b'00',
                 nHashFuncs: int = 0,
                 nTweak: int = 0,
                 nFlags: int = 0
                 ) -> None:
        self.data = data
        self.nHashFuncs = nHashFuncs
        self.nTweak = nTweak
        self.nFlags = nFlags

    def deserialize(self, f: BytesIO) -> None:
        self.data = deser_string(f)
        self.nHashFuncs = struct.unpack("<I", f.read(4))[0]
        self.nTweak = struct.unpack("<I", f.read(4))[0]
        self.nFlags = struct.unpack("<B", f.read(1))[0]

    def serialize(self) -> bytes:
        r = b""
        r += ser_string(self.data)
        r += struct.pack("<I", self.nHashFuncs)
        r += struct.pack("<I", self.nTweak)
        r += struct.pack("<B", self.nFlags)
        return r

    def __repr__(self) -> str:
        return f"msg_filterload(data={self.data!r}, nHashFuncs={self.nHashFuncs}," \
               f"nTweak={self.nTweak}, nFlags={self.nFlags})"


class msg_filteradd:
    __slots__ = ("data")
    msgtype = b"filteradd"

    def __init__(self, data: bytes) -> None:
        self.data = data

    def deserialize(self, f: BytesIO) -> None:
        self.data = deser_string(f)

    def serialize(self) -> bytes:
        r = b""
        r += ser_string(self.data)
        return r

    def __repr__(self) -> str:
        return f"msg_filteradd(data={self.data!r})"


class msg_filterclear:
    __slots__ = ()
    msgtype = b"filterclear"

    def __init__(self) -> None:
        pass

    def deserialize(self, f: BytesIO) -> None:
        pass

    def serialize(self) -> bytes:
        return b""

    def __repr__(self) -> str:
        return "msg_filterclear()"


class msg_feefilter:
    __slots__ = ("feerate",)
    msgtype = b"feefilter"

    def __init__(self, feerate: int = 0) -> None:
        self.feerate = feerate

    def deserialize(self, f: BytesIO) -> None:
        self.feerate = struct.unpack("<Q", f.read(8))[0]

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<Q", self.feerate)
        return r

    def __repr__(self) -> str:
        return "msg_feefilter(feerate=%08x)" % self.feerate


class msg_sendcmpct:
    __slots__ = ("announce", "version")
    msgtype = b"sendcmpct"

    def __init__(self) -> None:
        self.announce = False
        self.version = 1

    def deserialize(self, f: BytesIO) -> None:
        self.announce = struct.unpack("<?", f.read(1))[0]
        self.version = struct.unpack("<Q", f.read(8))[0]

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<?", self.announce)
        r += struct.pack("<Q", self.version)
        return r

    def __repr__(self) -> str:
        return "msg_sendcmpct(announce=%s, version=%lu)" % (self.announce, self.version)


class msg_cmpctblock:
    __slots__ = ("header_and_shortids",)
    msgtype = b"cmpctblock"

    def __init__(self,
                 header_and_shortids: Optional[P2PHeaderAndShortIDs] = None
                 ) -> None:
        self.header_and_shortids = header_and_shortids

    def deserialize(self, f: BytesIO) -> None:
        self.header_and_shortids = P2PHeaderAndShortIDs()
        self.header_and_shortids.deserialize(f)

    def serialize(self) -> bytes:
        assert self.header_and_shortids is not None
        r = b""
        r += self.header_and_shortids.serialize()
        return r

    def __repr__(self) -> str:
        return "msg_cmpctblock(HeaderAndShortIDs=%s)" % repr(self.header_and_shortids)


class msg_getblocktxn:
    __slots__ = ("block_txn_request",)
    msgtype = b"getblocktxn"

    def __init__(self) -> None:
        self.block_txn_request: Optional[BlockTransactionsRequest] = None

    def deserialize(self, f: BytesIO) -> None:
        self.block_txn_request = BlockTransactionsRequest()
        self.block_txn_request.deserialize(f)

    def serialize(self) -> bytes:
        assert self.block_txn_request is not None
        r = b""
        r += self.block_txn_request.serialize()
        return r

    def __repr__(self) -> str:
        return "msg_getblocktxn(block_txn_request=%s)" % (repr(self.block_txn_request))


class msg_blocktxn:
    __slots__ = ("block_transactions",)
    msgtype = b"blocktxn"

    def __init__(self) -> None:
        self.block_transactions = BlockTransactions()

    def deserialize(self, f: BytesIO) -> None:
        self.block_transactions.deserialize(f)

    def serialize(self) -> bytes:
        r = b""
        r += self.block_transactions.serialize()
        return r

    def __repr__(self) -> str:
        return "msg_blocktxn(block_transactions=%s)" % (repr(self.block_transactions))


class msg_no_witness_blocktxn(msg_blocktxn):
    __slots__ = ()

    def serialize(self) -> bytes:
        return self.block_transactions.serialize(with_witness=False)


class msg_getcfilters:
    __slots__ = ("filter_type", "start_height", "stop_hash")
    msgtype =  b"getcfilters"

    def __init__(self, filter_type: int, start_height: int, stop_hash: int) -> None:
        self.filter_type = filter_type
        self.start_height = start_height
        self.stop_hash = stop_hash

    def deserialize(self, f: BytesIO) -> None:
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.start_height = struct.unpack("<I", f.read(4))[0]
        self.stop_hash = deser_uint256(f)

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += struct.pack("<I", self.start_height)
        r += ser_uint256(self.stop_hash)
        return r

    def __repr__(self) -> str:
        return "msg_getcfilters(filter_type={:#x}, start_height={}, stop_hash={:x})".format(
            self.filter_type, self.start_height, self.stop_hash)

class msg_cfilter:
    __slots__ = ("filter_type", "block_hash", "filter_data")
    msgtype =  b"cfilter"

    def __init__(self,
                 filter_type: Optional[int] = None,
                 block_hash: Optional[int] = None,
                 filter_data: Optional[bytes] = None
                 ) -> None:
        self.filter_type = filter_type
        self.block_hash = block_hash
        self.filter_data = filter_data

    def deserialize(self, f: BytesIO) -> None:
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.block_hash = deser_uint256(f)
        self.filter_data = deser_string(f)

    def serialize(self) -> bytes:
        assert self.filter_type is not None and \
               self.block_hash is not None and \
               self.filter_data is not None
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += ser_uint256(self.block_hash)
        r += ser_string(self.filter_data)
        return r

    def __repr__(self) -> str:
        assert self.filter_type is not None and \
               self.block_hash is not None
        return "msg_cfilter(filter_type={:#x}, block_hash={:x})".format(
            self.filter_type, self.block_hash)

class msg_getcfheaders:
    __slots__ = ("filter_type", "start_height", "stop_hash")
    msgtype =  b"getcfheaders"

    def __init__(self, filter_type: int, start_height: int, stop_hash: int) -> None:
        self.filter_type = filter_type
        self.start_height = start_height
        self.stop_hash = stop_hash

    def deserialize(self, f: BytesIO) -> None:
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.start_height = struct.unpack("<I", f.read(4))[0]
        self.stop_hash = deser_uint256(f)

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += struct.pack("<I", self.start_height)
        r += ser_uint256(self.stop_hash)
        return r

    def __repr__(self) -> str:
        return "msg_getcfheaders(filter_type={:#x}, start_height={}, stop_hash={:x})".format(
            self.filter_type, self.start_height, self.stop_hash)

class msg_cfheaders:
    __slots__ = ("filter_type", "stop_hash", "prev_header", "hashes")
    msgtype =  b"cfheaders"

    def __init__(self,
                 filter_type: int,
                 stop_hash: int,
                 prev_header: int,
                 hashes: List[int]
                 ) -> None:
        self.filter_type = filter_type
        self.stop_hash = stop_hash
        self.prev_header = prev_header
        self.hashes = hashes

    def deserialize(self, f: BytesIO) -> None:
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.stop_hash = deser_uint256(f)
        self.prev_header = deser_uint256(f)
        self.hashes = deser_uint256_vector(f)

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += ser_uint256(self.stop_hash)
        r += ser_uint256(self.prev_header)
        r += ser_uint256_vector(self.hashes)
        return r

    def __repr__(self) -> str:
        return "msg_cfheaders(filter_type={:#x}, stop_hash={:x})".format(
            self.filter_type, self.stop_hash)

class msg_getcfcheckpt:
    __slots__ = ("filter_type", "stop_hash")
    msgtype =  b"getcfcheckpt"

    def __init__(self, filter_type: int, stop_hash: int) -> None:
        self.filter_type = filter_type
        self.stop_hash = stop_hash

    def deserialize(self, f: BytesIO) -> None:
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.stop_hash = deser_uint256(f)

    def serialize(self) -> bytes:
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += ser_uint256(self.stop_hash)
        return r

    def __repr__(self) -> str:
        return "msg_getcfcheckpt(filter_type={:#x}, stop_hash={:x})".format(
            self.filter_type, self.stop_hash)

class msg_cfcheckpt:
    __slots__ = ("filter_type", "stop_hash", "headers")
    msgtype =  b"cfcheckpt"

    def __init__(self,
                 filter_type: Optional[int] = None,
                 stop_hash: Optional[int] = None,
                 headers: Optional[List[int]] = None
                 ) -> None:
        self.filter_type = filter_type
        self.stop_hash = stop_hash
        self.headers = headers

    def deserialize(self, f: BytesIO) -> None:
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.stop_hash = deser_uint256(f)
        self.headers = deser_uint256_vector(f)

    def serialize(self) -> bytes:
        assert self.filter_type is not None and \
               self.stop_hash is not None and \
               self.headers is not None
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += ser_uint256(self.stop_hash)
        r += ser_uint256_vector(self.headers)
        return r

    def __repr__(self) -> str:
        assert self.filter_type is not None and \
               self.stop_hash is not None
        return "msg_cfcheckpt(filter_type={:#x}, stop_hash={:x})".format(
            self.filter_type, self.stop_hash)
