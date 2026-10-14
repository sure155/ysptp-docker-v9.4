#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations

import argparse
import atexit
import base64
import binascii
import collections
import contextlib
import dataclasses
import datetime
import functools
import gzip
import hashlib
import hmac as _hmac
import http.client
import http.cookiejar
import json
import math
import os
import random
import re
import secrets
import shutil
import signal
import socket
import ssl
import struct
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from collections import OrderedDict, deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# 全局禁用环境代理 (与原版一致)
urllib.request.install_opener(urllib.request.build_opener(urllib.request.ProxyHandler({})))

__version__ = '9.4.1'
AUTHOR_COMMUNITY = 'https://t.me/garysclub'
AUTHOR_CHANNEL = 'https://t.me/garysclubchannel'
AUTHOR_NOTICE = f'首发社区: {AUTHOR_COMMUNITY} | 首发频道: {AUTHOR_CHANNEL} (其他渠道均非作者发布！)'

AK = '9f5c54c4ed0e50109b800f7e28fec205'
RSA_PUBLIC_KEY_B64 = 'MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAkKeLy4ywWLSnBkwRyqYgF3HMIj05V5uuh5HjyEsZOWnu1NHu3jPQv3sr32wwQNYv5qapsNXmNgLUDHtgHZxqPQAYXltjSRc0qhcD286t62wOIHId8zXS3s1Jy4rgU4qjQWzI9rp/1sE0pMsmwTaJa4zuJ5iz8VwF8Av5oJ1k+HxY+/HLnjNlW1hmWLpuDYmkZYuAoTHa1VGeHQh9FEKI8ZcL3GTQphShUoC+Kg3P1hGUVTtCYapmzPS5lkAdwebuzwvTCfGiTErYZCnPBUSeV7BVlgjtLYIi29KvF0a8FHsJMfe/UdHcyW/RihsIYOtDQcRRpFGXyPXbVrzFJse24QIDAQAB'
CLOUD_GET_URL = 'https://ytpcloudws.cctv.cn/cloudps/wssapi/device/v2/get'
CLOUD_REGISTER_URL = 'https://ytpcloudws.cctv.cn/cloudps/wssapi/device/v2/register'
APP_START_URL = 'https://ytpaddr.cctv.cn/gsnw/api/app/start/v1/01'
DRM_CONFIG_URL = 'https://ytpaddr.cctv.cn/gsnw/drm/config/obtain/v1'
VERSION_CONFIG_URL = 'https://ytpaddr.cctv.cn/gsnw/version/config/obtain/v1'
DICTIONARY_URL = 'https://ytpaddr.cctv.cn/gsnw/player/dictionary/obtain/v1'
INDEX_URL = 'https://ytpaddr.cctv.cn/gsnw/api/index/v1/01'
REPORT_SINGLE_URL = 'https://ytpdata.cctv.cn/das/app/data/message/single'
COLLECT_REPORT_URL = 'https://collect.cctv.cn/cctvmobileinf/rest/cctv/receive/new/app'
LIVE_V1_01_URL = 'https://ytpaddr.cctv.cn/gsnw/api/live/v1/01'
LIVE_V1_02_URL = 'https://ytpaddr.cctv.cn/gsnw/api/live/v1/02'
VDN_GETSTREAM_URL = 'https://ytpvdn.cctv.cn/cctvmobileinf/rest/cctv/videoliveUrl/getstream'
DEFAULT_LIVE_USER_ID = 'BAEBFF2B-C516-4F34-ABC0-A824A6461CBD'
DEFAULT_DEVICE_NAME = '央视频电视投屏助手'
VDN_APP_NAME = '央视频电视投屏助手'
REPORT_APP_KEY = '1178c84d-4818-44ff-b415-02106e87e144'
COLLECT_SDK_VERSION = '1.0.0'
DEFAULT_PAGE_NAME = 'com.cctv.tv.mvp.ui.activity.MainActivity'
DEFAULT_ACCEPT_LANGUAGE = 'zh-CN,zh;q=0.8'

RESULT_OK = 0
RESULT_NEEDS_REGISTER = 601
RESULT_GET_MISSING_OR_INVALID = 2
RESULT_REGISTERED_ELSEWHERE = 694
RESULT_REGISTER_RETRY_LATER = 695

# ---------------------------------------------------------------------------
# 纯 Python AES-256-GCM / RSA-OAEP (零依赖)
# 优化: S-box 由算法生成 (去掉 256 项硬编码表); 密钥扩展加 lru_cache,
#       原版每加密一个 16 字节块都会重算一次完整密钥扩展。
# ---------------------------------------------------------------------------


def _build_sbox() -> tuple:
    sbox = [0] * 256
    p = q = 1
    while True:
        p = (p ^ (p << 1) ^ (0x1B if p & 0x80 else 0)) & 0xFF
        q = (q ^ (q << 1)) & 0xFF
        q = (q ^ (q << 2)) & 0xFF
        q = (q ^ (q << 4)) & 0xFF
        if q & 0x80:
            q ^= 0x09

        def rotl(x, n):
            return ((x << n) | (x >> (8 - n))) & 0xFF

        sbox[p] = (q ^ rotl(q, 1) ^ rotl(q, 2) ^ rotl(q, 3) ^ rotl(q, 4) ^ 0x63) & 0xFF
        if p == 1:
            break
    sbox[0] = 0x63
    return tuple(sbox)


_SBOX = _build_sbox()
_RCON = (1, 2, 4, 8, 16, 32, 64, 128, 27, 54)


def _xtime(a: int) -> int:
    return ((a << 1) ^ 0x11B) & 0xFF if a & 0x80 else (a << 1) & 0xFF


@functools.lru_cache(maxsize=16)
def _aes256_key_schedule(key: bytes) -> tuple:
    assert len(key) == 32
    w = [int.from_bytes(key[i:i + 4], 'big') for i in range(0, 32, 4)]
    for i in range(8, 60):
        temp = w[i - 1]
        if i % 8 == 0:
            temp = (_SBOX[(temp >> 16) & 255] << 24 | _SBOX[(temp >> 8) & 255] << 16
                    | _SBOX[temp & 255] << 8 | _SBOX[(temp >> 24) & 255])
            temp ^= _RCON[i // 8 - 1] << 24
        elif i % 8 == 4:
            temp = (_SBOX[(temp >> 24) & 255] << 24 | _SBOX[(temp >> 16) & 255] << 16
                    | _SBOX[(temp >> 8) & 255] << 8 | _SBOX[temp & 255])
        w.append(w[i - 8] ^ temp)
    return tuple(b''.join(word.to_bytes(4, 'big') for word in w[i:i + 4]) for i in range(0, 60, 4))


def _add_round_key(state, rk: bytes):
    for i in range(16):
        state[i] ^= rk[i]


def _sub_bytes(state):
    for i in range(16):
        state[i] = _SBOX[state[i]]


def _shift_rows(s):
    s[1], s[5], s[9], s[13] = s[5], s[9], s[13], s[1]
    s[2], s[6], s[10], s[14] = s[10], s[14], s[2], s[6]
    s[3], s[7], s[11], s[15] = s[15], s[3], s[7], s[11]


def _mix_columns(s):
    for c in range(4):
        a0, a1, a2, a3 = s[4 * c], s[4 * c + 1], s[4 * c + 2], s[4 * c + 3]
        s[4 * c] = _xtime(a0) ^ (_xtime(a1) ^ a1) ^ a2 ^ a3
        s[4 * c + 1] = a0 ^ _xtime(a1) ^ (_xtime(a2) ^ a2) ^ a3
        s[4 * c + 2] = a0 ^ a1 ^ _xtime(a2) ^ (_xtime(a3) ^ a3)
        s[4 * c + 3] = (_xtime(a0) ^ a0) ^ a1 ^ a2 ^ _xtime(a3)


def aes256_encrypt_block(key: bytes, block: bytes) -> bytes:
    rk = _aes256_key_schedule(key)
    s = bytearray(block)
    _add_round_key(s, rk[0])
    for rnd in range(1, 14):
        _sub_bytes(s)
        _shift_rows(s)
        _mix_columns(s)
        _add_round_key(s, rk[rnd])
    _sub_bytes(s)
    _shift_rows(s)
    _add_round_key(s, rk[14])
    return bytes(s)


_GCM_R = 0xE1 << 120
_GCM_TOP = 1 << 127
_MASK128 = (1 << 128) - 1


def _gf_mult(x: int, y: int) -> int:
    z = 0
    v = y
    for _ in range(128):
        if x & _GCM_TOP:
            z ^= v
        v = (v >> 1) ^ _GCM_R if v & 1 else v >> 1
        x = (x << 1) & _MASK128
    return z


def _ghash(h: int, aad: bytes, ct: bytes) -> int:
    x = 0

    def _blocks(data: bytes):
        for i in range(0, len(data), 16):
            blk = data[i:i + 16]
            if len(blk) < 16:
                blk = blk + b'\x00' * (16 - len(blk))
            yield int.from_bytes(blk, 'big')

    for b in _blocks(aad):
        x = _gf_mult(x ^ b, h)
    for b in _blocks(ct):
        x = _gf_mult(x ^ b, h)
    lens = ((len(aad) * 8) << 64) | (len(ct) * 8)
    return _gf_mult(x ^ lens, h)


def _inc32(block: bytes) -> bytes:
    ctr = int.from_bytes(block[12:], 'big')
    return block[:12] + ((ctr + 1) & 0xFFFFFFFF).to_bytes(4, 'big')


def _gctr(key: bytes, icb: bytes, data: bytes) -> bytes:
    out = bytearray()
    cb = icb
    for i in range(0, len(data), 16):
        ks = aes256_encrypt_block(key, cb)
        chunk = data[i:i + 16]
        out += bytes(a ^ b for a, b in zip(chunk, ks))
        cb = _inc32(cb)
    return bytes(out)


def aes_gcm_encrypt(key: bytes, nonce: bytes, plaintext: bytes, aad: bytes = b'') -> bytes:
    assert len(key) == 32 and len(nonce) == 12
    h = int.from_bytes(aes256_encrypt_block(key, b'\x00' * 16), 'big')
    j0 = nonce + b'\x00\x00\x00\x01'
    ct = _gctr(key, _inc32(j0), plaintext)
    s = _ghash(h, aad, ct).to_bytes(16, 'big')
    tag = bytes(a ^ b for a, b in zip(aes256_encrypt_block(key, j0), s))
    return ct + tag


def aes_gcm_decrypt(key: bytes, nonce: bytes, ct_and_tag: bytes, aad: bytes = b'') -> bytes:
    if len(ct_and_tag) < 16:
        raise ValueError('AES-GCM payload too short')
    ct, tag = ct_and_tag[:-16], ct_and_tag[-16:]
    h = int.from_bytes(aes256_encrypt_block(key, b'\x00' * 16), 'big')
    j0 = nonce + b'\x00\x00\x00\x01'
    s = _ghash(h, aad, ct).to_bytes(16, 'big')
    expect = bytes(a ^ b for a, b in zip(aes256_encrypt_block(key, j0), s))
    if not _hmac.compare_digest(tag, expect):
        raise ValueError('AES-GCM decrypt failed')
    return _gctr(key, _inc32(j0), ct)


def _mgf1_sha256(seed: bytes, length: int) -> bytes:
    out = bytearray()
    counter = 0
    while len(out) < length:
        out += hashlib.sha256(seed + counter.to_bytes(4, 'big')).digest()
        counter += 1
    return bytes(out[:length])


def _oaep_encode_sha256(message: bytes, k: int, seed: bytes) -> bytes:
    hlen = 32
    if len(message) > k - 2 * hlen - 2:
        raise ValueError('OAEP message too long')
    lhash = hashlib.sha256(b'').digest()
    ps = b'\x00' * (k - len(message) - 2 * hlen - 2)
    db = lhash + ps + b'\x01' + message
    db_mask = _mgf1_sha256(seed, k - hlen - 1)
    masked_db = bytes(a ^ b for a, b in zip(db, db_mask))
    seed_mask = _mgf1_sha256(masked_db, hlen)
    masked_seed = bytes(a ^ b for a, b in zip(seed, seed_mask))
    return b'\x00' + masked_seed + masked_db


def _der_read_len(der: bytes, pos: int):
    first = der[pos]
    pos += 1
    if first & 0x80 == 0:
        return first, pos
    n = first & 0x7F
    return int.from_bytes(der[pos:pos + n], 'big'), pos + n


def _der_read_tlv(der: bytes, pos: int):
    assert der[pos] == 0x30, 'expected SEQUENCE'
    pos += 1
    ln, pos = _der_read_len(der, pos)
    end = pos + ln
    items = []
    while pos < end:
        tag = der[pos]
        pos += 1
        ln2, pos = _der_read_len(der, pos)
        items.append((tag, der[pos:pos + ln2]))
        pos += ln2
    return items


def parse_spki_rsa_pubkey(der: bytes):
    outer = _der_read_tlv(der, 0)
    bitstring = outer[1][1]
    assert bitstring[0] == 0
    inner = _der_read_tlv(bitstring[1:], 0)
    return int.from_bytes(inner[0][1], 'big'), int.from_bytes(inner[1][1], 'big')


def rsa_oaep_sha256_encrypt(n: int, e: int, message: bytes, seed: bytes) -> bytes:
    k = (n.bit_length() + 7) // 8
    em = _oaep_encode_sha256(message, k, seed)
    return pow(int.from_bytes(em, 'big'), e, n).to_bytes(k, 'big')


# ---------------------------------------------------------------------------
# 通用工具
# ---------------------------------------------------------------------------


class YsptpError(Exception):
    pass


def now_f64() -> float:
    return time.time()


def current_time_ms() -> int:
    return int(now_f64() * 1000.0)


def rust_round(x: float) -> float:
    return math.floor(x + 0.5)


def sha1_upper(value: str) -> str:
    return hashlib.sha1(value.encode('utf-8')).hexdigest().upper()


def sha256_hex(value: str) -> str:
    return hashlib.sha256(value.encode('utf-8')).hexdigest()


def md5_hex(value: str) -> str:
    return hashlib.md5(value.encode('utf-8')).hexdigest()


global_log_ring = collections.deque(maxlen=120)
_log_lock = threading.Lock()
_last_log_times: dict = {}


def log(msg, min_interval=0.0):
    now = time.time()
    clean_msg = str(msg).strip()
    if not clean_msg:
        return
    with _log_lock:
        interval = min_interval if min_interval > 0.0 else 1.5
        if now - _last_log_times.get(clean_msg, 0.0) < interval:
            return
        _last_log_times[clean_msg] = now
        if len(_last_log_times) > 600:
            _last_log_times.clear()
        line = '[%s] %s' % (time.strftime('%H:%M:%S'), clean_msg)
        global_log_ring.append(line)
    print(line, flush=True)


def java_string_hashcode(value: str) -> int:
    h = 0
    for ch in value:
        h = (h * 31 + ord(ch)) & 0xFFFFFFFF
    return h - 0x100000000 if h & 0x80000000 else h


def java_uuid_from_hashes(msb_hash: int, lsb_hash: int) -> str:
    msb = msb_hash & 0xFFFFFFFFFFFFFFFF
    lsb = lsb_hash & 0xFFFFFFFFFFFFFFFF
    return f'{(msb << 64) | lsb:032x}'


def native_day0_ms(now_s: int) -> int:
    return 86400000 * ((now_s + 28800) // 86400) - 28800000


def compute_fingerprint(x_uid: str, now_ms: int):
    day0_ms = native_day0_ms(now_ms // 1000)
    first = sha256_hex(f'{AK}{x_uid}{now_ms}{day0_ms}')
    return sha256_hex(first), now_ms, day0_ms


def random_hex_string(length: int) -> str:
    return ''.join(secrets.choice('0123456789abcdef') for _ in range(length))


def random_mac_address() -> str:
    raw = bytearray(secrets.token_bytes(6))
    raw[0] = (raw[0] | 2) & 254
    return ':'.join(f'{b:02x}' for b in raw)


def sanitize_profile_id(value: str) -> str:
    out = []
    last_underscore = False
    for ch in value:
        if ch.isascii() and ch.isalnum():
            out.append(ch.lower())
            last_underscore = False
        elif not last_underscore:
            out.append('_')
            last_underscore = True
    return ''.join(out).strip('_')


def resolution_from_screen_param(screen_param: str) -> str:
    parts = screen_param.split('-')
    if len(parts) >= 2 and parts[0] and parts[1]:
        return f'{parts[0]}*{parts[1]}'
    return '3840*2160'


# 设备协议 (高码率) 频道: (slug, live_id)
_DEVICE_CHANNELS = (
    ('cctv1', 'Live1717729995180256'), ('cctv2', 'Live1718261577870260'),
    ('cctv3', 'Live1718261955077261'), ('cctv4', 'Live1718276148119264'),
    ('cctv5', 'Live1719474204987287'), ('cctv5p', 'Live1719473996025286'),
    ('cctv7', 'Live1718276412224269'), ('cctv8', 'Live1718276458899270'),
    ('cctv9', 'Live1718276503187272'), ('cctv10', 'Live1718276550002273'),
    ('cctv11', 'Live1718276603690275'), ('cctv12', 'Live1718276623932276'),
    ('cctv13', 'Live1718276575708274'), ('cctv14', 'Live1718276498748271'),
    ('cctv15', 'Live1718276319614267'), ('cctv16', 'Live1718276256572265'),
    ('cctv17', 'Live1718276138318263'), ('cctv4k', 'Live1767871224782105'),
    ('cctv8k', 'Live1688400593818102'), ('cctv164k', 'Live1704966749996185'),
    ('cgtn', 'Live1719392219423280'), ('cgtnfr', 'Live1719392670442283'),
    ('cgtnru', 'Live1719392779653284'), ('cgtnar', 'Live1719392885692285'),
    ('cgtnes', 'Live1719392560433282'), ('cgtndoc', 'Live1719392360336281'),
)
_DEVICE_LIVE_IDS = dict(_DEVICE_CHANNELS)


def channels():
    return list(_DEVICE_CHANNELS)


def channel_by_name(name: str):
    return _DEVICE_LIVE_IDS.get(name)


def normalize_channel(raw: str) -> str:
    key = raw.strip().strip('/').lower()
    if key.endswith('.m3u8'):
        key = key[:-len('.m3u8')]
    if key in ('cctv16-4k', 'cctv16_4k', 'cctv16/4k', 'cctv16(4k)'):
        return 'cctv164k'
    return key


def cooldown_for(fail_count: int) -> float:
    """高码率频道连续失败后的冷却秒数 (15 / 60 / 120)。"""
    if fail_count <= 1:
        return 15.0
    if fail_count == 2:
        return 60.0
    return 120.0


TRUE_4K_CHANNELS = {'cctv4k', 'cctv8k', 'cctv164k'}


# ---------------------------------------------------------------------------
# 数据结构
# ---------------------------------------------------------------------------


@dataclasses.dataclass
class DeviceProfile:
    android_id: str = ''
    mac: str = ''
    hardware: str = ''
    board: str = ''
    brand: str = ''
    device: str = ''
    manufacturer: str = ''
    model: str = ''
    product: str = ''
    tags: str = ''
    build_type: str = ''
    user: str = ''
    resolution: str = ''
    display: str = ''
    version_id: str = ''
    host: str = ''
    fingerprint: str = ''
    report_model: str = ''

    @classmethod
    def from_dict(cls, d: dict) -> 'DeviceProfile':
        return cls(**{f.name: str(d.get(f.name, '')) for f in dataclasses.fields(cls)})


@dataclasses.dataclass
class DeviceState:
    schema_version: int = 1
    profile_source: str = ''
    profile: DeviceProfile = dataclasses.field(default_factory=DeviceProfile)
    screen_param: str = ''
    cast_model: str = ''
    x_uid: str = ''
    cloud_guid: str = ''
    registered_at: float = 0.0
    updated_at: float = 0.0


@dataclasses.dataclass
class Identity:
    x_uid: str = ''
    x_fingerprint: str = ''
    fingerprint_timestamp_ms: int = 0
    headers: dict = dataclasses.field(default_factory=dict)


@dataclasses.dataclass
class ChannelEntry:
    channel: str = ''
    live_id: str = ''
    final_url: str = ''
    playback_headers: dict = dataclasses.field(default_factory=dict)
    android_id: str = ''
    x_uid: str = ''
    rate: str = ''
    rate_name: str = ''
    raw_live_host: str = ''
    final_host: str = ''
    refreshed_at: float = 0.0
    expires_at: float = 0.0
    generation: int = 0
    last_refresh_error: str = ''
    last_refresh_failed_at: float = 0.0
    session_generation: int = 0

    def fresh(self, now: float) -> bool:
        return bool(self.final_url) and now < self.expires_at

    @classmethod
    def from_dict(cls, d: dict) -> 'ChannelEntry':
        kwargs = {}
        for f in dataclasses.fields(cls):
            v = d.get(f.name, f.default if f.default is not dataclasses.MISSING else None)
            if f.name == 'playback_headers':
                v = dict(v) if isinstance(v, dict) else {}
            kwargs[f.name] = v
        return cls(**kwargs)


@dataclasses.dataclass
class PlaylistCacheEntry:
    body: str = ''
    content_type: str = ''
    cached_at: float = 0.0
    expires_at: float = 0.0
    final_url: str = ''
    android_id: str = ''
    proxy_origin: str = ''
    proxy_prefix: str = ''


@dataclasses.dataclass
class PlaylistCacheProbe:
    state: str = ''
    age_ms: int | None = None


@dataclasses.dataclass
class AppStartResult:
    session_key: str = ''


@dataclasses.dataclass
class Live01Result:
    live_url: str = ''
    rate: str = ''
    rate_name: str = ''


@dataclasses.dataclass
class VdnGetStreamResult:
    final_url: str = ''
    app_sign: str = ''
    app_random_str: str = ''


def inspect_playlist_cache(cached, entry: ChannelEntry, proxy_origin: str, proxy_prefix, now: float) -> PlaylistCacheProbe:
    if cached is None:
        return PlaylistCacheProbe(state='miss:not_found', age_ms=None)
    age_ms = int(rust_round(max(0.0, now - cached.cached_at) * 1000.0))
    checks = (
        ('expired', now < cached.expires_at),
        ('final_url_changed', cached.final_url == entry.final_url),
        ('android_id_changed', cached.android_id == entry.android_id),
        ('origin_changed', cached.proxy_origin == proxy_origin),
        ('prefix_changed', cached.proxy_prefix == (proxy_prefix or '')),
    )
    reasons = [name for name, ok in checks if not ok]
    if not reasons:
        return PlaylistCacheProbe(state='hit', age_ms=age_ms)
    return PlaylistCacheProbe(state='miss:' + '+'.join(reasons), age_ms=age_ms)


# ---------------------------------------------------------------------------
# 设备资料池
# 压缩为紧凑元组后展开 (展开结果与原版 DEVICE_PROFILE_POOL 逐项一致):
#   (brand, manufacturer, model, hardware, board, version_id, screen_param)
#   source = <brand>_<8k|4k>_pool.<model 去空格>
#   report_model = model 去掉 '-' 和空格, cast_model = model
# ---------------------------------------------------------------------------
_POOL_ROWS = (
    # Sony 8K
    ('Sony', 'Sony', 'XR-85Z9K', 'mt5895', 'mt5895', 'SONYTV.2022.XR_85Z9K', '7680-4320-280'),
    ('Sony', 'Sony', 'XR-75Z9K', 'mt5895', 'mt5895', 'SONYTV.2022.XR_75Z9K', '7680-4320-260'),
    ('Sony', 'Sony', 'XR-85Z9J', 'mt5895', 'mt5895', 'SONYTV.2021.XR_85Z9J', '7680-4320-280'),
    ('Sony', 'Sony', 'XR-75Z9J', 'mt5895', 'mt5895', 'SONYTV.2021.XR_75Z9J', '7680-4320-260'),
    ('Sony', 'Sony', 'KD-98ZG9', 'mt5893', 'mt5893', 'SONYTV.2019.KD_98ZG9', '7680-4320-320'),
    ('Sony', 'Sony', 'KD-85ZG9', 'mt5893', 'mt5893', 'SONYTV.2019.KD_85ZG9', '7680-4320-280'),
    ('Sony', 'Sony', 'KD-85ZH8', 'mt5893', 'mt5893', 'SONYTV.2020.KD_85ZH8', '7680-4320-280'),
    ('Sony', 'Sony', 'KD-75ZH8', 'mt5893', 'mt5893', 'SONYTV.2020.KD_75ZH8', '7680-4320-260'),
    # Samsung 8K
    ('Samsung', 'Samsung', 'QA85QN900A', 's5e9925', 'neo8k', 'SAMSUNGTV.2021.QN900A', '7680-4320-280'),
    ('Samsung', 'Samsung', 'QA75QN900A', 's5e9925', 'neo8k', 'SAMSUNGTV.2021.QN900A', '7680-4320-260'),
    ('Samsung', 'Samsung', 'QA85QN900B', 's5e9925', 'neo8k', 'SAMSUNGTV.2022.QN900B', '7680-4320-280'),
    ('Samsung', 'Samsung', 'QA75QN900B', 's5e9925', 'neo8k', 'SAMSUNGTV.2022.QN900B', '7680-4320-260'),
    ('Samsung', 'Samsung', 'QA85QN900C', 's5e9935', 'neo8k', 'SAMSUNGTV.2023.QN900C', '7680-4320-280'),
    ('Samsung', 'Samsung', 'QA75QN900C', 's5e9935', 'neo8k', 'SAMSUNGTV.2023.QN900C', '7680-4320-260'),
    ('Samsung', 'Samsung', 'QA85QN900D', 's5e9945', 'neo8k', 'SAMSUNGTV.2024.QN900D', '7680-4320-280'),
    ('Samsung', 'Samsung', 'QA98QN990C', 's5e9935', 'neo8k', 'SAMSUNGTV.2023.QN990C', '7680-4320-320'),
    ('Samsung', 'Samsung', 'QA85QN800C', 's5e9935', 'neo8k', 'SAMSUNGTV.2023.QN800C', '7680-4320-280'),
    ('Samsung', 'Samsung', 'QA75QN800D', 's5e9945', 'neo8k', 'SAMSUNGTV.2024.QN800D', '7680-4320-260'),
    # LG 8K
    ('LG', 'LGE', 'OLED88Z1PCA', 'alpha9gen4', 'lg8k', 'LGTV.2021.OLED88Z1', '7680-4320-320'),
    ('LG', 'LGE', 'OLED77Z1PCA', 'alpha9gen4', 'lg8k', 'LGTV.2021.OLED77Z1', '7680-4320-260'),
    ('LG', 'LGE', 'OLED88Z2PCA', 'alpha9gen5', 'lg8k', 'LGTV.2022.OLED88Z2', '7680-4320-320'),
    ('LG', 'LGE', 'OLED77Z2PCA', 'alpha9gen5', 'lg8k', 'LGTV.2022.OLED77Z2', '7680-4320-260'),
    ('LG', 'LGE', 'OLED88Z3PCA', 'alpha9gen6', 'lg8k', 'LGTV.2023.OLED88Z3', '7680-4320-320'),
    ('LG', 'LGE', 'OLED77Z3PCA', 'alpha9gen6', 'lg8k', 'LGTV.2023.OLED77Z3', '7680-4320-260'),
    ('LG', 'LGE', 'OLED88Z4PCA', 'alpha9gen7', 'lg8k', 'LGTV.2024.OLED88Z4', '7680-4320-320'),
    ('LG', 'LGE', '86QNED99', 'alpha9gen4', 'lg8k', 'LGTV.2021.86QNED99', '7680-4320-300'),
    # Sony 4K
    ('Sony', 'Sony', 'XR-85X95K', 'mt5895', 'mt5895', 'SONYTV.2022.XR_85X95K', '3840-2160-300'),
    ('Sony', 'Sony', 'XR-75X95K', 'mt5895', 'mt5895', 'SONYTV.2022.XR_75X95K', '3840-2160-280'),
    ('Sony', 'Sony', 'XR-65X90K', 'mt5895', 'mt5895', 'SONYTV.2022.XR_65X90K', '3840-2160-260'),
    ('Sony', 'Sony', 'XR-55X90K', 'mt5895', 'mt5895', 'SONYTV.2022.XR_55X90K', '3840-2160-240'),
    ('Sony', 'Sony', 'XR-65A95K', 'mt5895', 'mt5895', 'SONYTV.2022.XR_65A95K', '3840-2160-260'),
    # Samsung 4K
    ('Samsung', 'Samsung', 'QA85QN90C', 's5e9935', 'neo4k', 'SAMSUNGTV.2023.QN90C', '3840-2160-300'),
    ('Samsung', 'Samsung', 'QA75QN90C', 's5e9935', 'neo4k', 'SAMSUNGTV.2023.QN90C', '3840-2160-280'),
    ('Samsung', 'Samsung', 'QA65QN90C', 's5e9935', 'neo4k', 'SAMSUNGTV.2023.QN90C', '3840-2160-260'),
    ('Samsung', 'Samsung', 'QA55QN90C', 's5e9935', 'neo4k', 'SAMSUNGTV.2023.QN90C', '3840-2160-240'),
    ('Samsung', 'Samsung', 'QA65S95C', 's5e9935', 'oled4k', 'SAMSUNGTV.2023.S95C', '3840-2160-260'),
    # LG 4K
    ('LG', 'LGE', 'OLED83C3PCA', 'alpha9gen6', 'lg4k', 'LGTV.2023.OLED83C3', '3840-2160-300'),
    ('LG', 'LGE', 'OLED77C3PCA', 'alpha9gen6', 'lg4k', 'LGTV.2023.OLED77C3', '3840-2160-280'),
    ('LG', 'LGE', 'OLED65C3PCA', 'alpha9gen6', 'lg4k', 'LGTV.2023.OLED65C3', '3840-2160-260'),
    ('LG', 'LGE', 'OLED55C3PCA', 'alpha9gen6', 'lg4k', 'LGTV.2023.OLED55C3', '3840-2160-240'),
    ('LG', 'LGE', '86QNED90', 'alpha7gen5', 'lg4k', 'LGTV.2022.86QNED90', '3840-2160-300'),
    # TCL
    ('TCL', 'TCL', '85X925 PRO', 'mt9615', 'tcl8k', 'TCLTV.2021.X925PRO', '7680-4320-280'),
    ('TCL', 'TCL', '75X925 PRO', 'mt9615', 'tcl8k', 'TCLTV.2021.X925PRO', '7680-4320-260'),
    ('TCL', 'TCL', '85C845', 'mt9615', 'tcl4k', 'TCLTV.2023.C845', '3840-2160-300'),
    ('TCL', 'TCL', '75C845', 'mt9615', 'tcl4k', 'TCLTV.2023.C845', '3840-2160-280'),
    ('TCL', 'TCL', '65C845', 'mt9615', 'tcl4k', 'TCLTV.2023.C845', '3840-2160-260'),
    ('TCL', 'TCL', '75C745', 'mt9615', 'tcl4k', 'TCLTV.2023.C745', '3840-2160-280'),
    ('TCL', 'TCL', '65C745', 'mt9615', 'tcl4k', 'TCLTV.2023.C745', '3840-2160-260'),
    # Changhong 4K
    ('CHANGHONG', 'CHANGHONG', 'U65G7', 'mt9632', 'changhong4k', 'CHANGHONGTV.2022.U65G7', '3840-2160-260'),
    ('CHANGHONG', 'CHANGHONG', 'U55G7', 'mt9632', 'changhong4k', 'CHANGHONGTV.2022.U55G7', '3840-2160-240'),
    ('CHANGHONG', 'CHANGHONG', 'L55QCN1', 'mt9632', 'changhong4k', 'CHANGHONGTV.2021.L55QCN1', '3840-2160-240'),
    ('CHANGHONG', 'CHANGHONG', 'U43QCN1', 'mt9632', 'changhong4k', 'CHANGHONGTV.2021.U43QCN1', '3840-2160-220'),
    ('CHANGHONG', 'CHANGHONG', 'UD65YC5500UA', 'mt9632', 'changhong4k', 'CHANGHONGTV.2020.UD65YC5500UA', '3840-2160-260'),
)


def _expand_pool_row(row) -> dict:
    brand, manufacturer, model, hardware, board, version_id, screen_param = row
    tier = '8k' if screen_param.startswith('7680') else '4k'
    return {
        'source': f"{brand.lower()}_{tier}_pool.{model.replace(' ', '')}",
        'brand': brand,
        'manufacturer': manufacturer,
        'model': model,
        'report_model': model.replace('-', '').replace(' ', ''),
        'hardware': hardware,
        'board': board,
        'version_id': version_id,
        'screen_param': screen_param,
        'cast_model': model,
    }


DEVICE_PROFILE_POOL = [_expand_pool_row(r) for r in _POOL_ROWS]


def random_device_template() -> dict:
    pool_8k = [t for t in DEVICE_PROFILE_POOL if '8k' in t.get('source', '')]
    return secrets.choice(pool_8k if pool_8k else DEVICE_PROFILE_POOL)


def device_profile_from_template(template: dict, android_id: str, mac: str) -> DeviceProfile:
    brand_id = sanitize_profile_id(template['brand'])
    model_id = sanitize_profile_id(template['model'])
    device = f'{brand_id}_{model_id}'
    product = f'{brand_id}_{model_id}'
    return DeviceProfile(
        android_id=android_id, mac=mac,
        hardware=template['hardware'], board=template['board'], brand=template['brand'],
        device=device, manufacturer=template['manufacturer'], model=template['model'],
        product=product, tags='release-keys', build_type='user', user='build',
        resolution=resolution_from_screen_param(template['screen_param']),
        display=f"{template['model']}-user 13 {template['version_id']} 2024 release-keys",
        version_id=template['version_id'], host=f'{brand_id}-tv-build',
        fingerprint=f"{template['manufacturer']}/{product}/{device}:13/{template['version_id']}/2024:user/release-keys",
        report_model=template['report_model'])


def infer_os_version(profile: DeviceProfile) -> str:
    if ':' in profile.fingerprint:
        tail = profile.fingerprint.split(':', 1)[1]
        if '/' in tail:
            return tail.split('/', 1)[0]
    return ''


def infer_sdk_int(profile: DeviceProfile) -> str:
    os_ver = infer_os_version(profile)
    major = os_ver.split('.')[0] if os_ver else ''
    return {'13': '33', '12': '31', '11': '30', '10': '29', '9': '28', '8': '26', '7': '24', '6': '23'}.get(major, '')


def compute_x_uid(profile: DeviceProfile) -> str:
    build_identity_str = ('1698' + profile.hardware + profile.board + profile.brand + profile.device
                          + profile.manufacturer + profile.model + profile.product + profile.tags
                          + profile.build_type + profile.user + profile.resolution + profile.mac)
    uuid_part = java_uuid_from_hashes(java_string_hashcode(build_identity_str), java_string_hashcode(profile.model))
    return sha1_upper(f'{profile.android_id}|{uuid_part}')


def default_device_state() -> DeviceState:
    template = random_device_template()
    profile = device_profile_from_template(template, random_hex_string(16), random_mac_address())
    return DeviceState(schema_version=1, profile_source=template['source'], profile=profile,
                       screen_param=template['screen_param'], cast_model=template['cast_model'],
                       x_uid=compute_x_uid(profile), cloud_guid='', registered_at=0.0, updated_at=now_f64())


def binary_dir() -> str:
    return os.path.dirname(os.path.abspath(__file__)) or '.'


def load_device_state(path: str):
    try:
        with open(path, encoding='utf-8') as f:
            text = f.read()
    except OSError:
        return default_device_state(), False
    try:
        data = json.loads(text)
    except ValueError:
        return default_device_state(), False
    try:
        profile = DeviceProfile.from_dict(data.get('profile', {}))
        state = DeviceState(
            schema_version=int(data.get('schema_version', 1)),
            profile_source=str(data.get('profile_source', '')),
            profile=profile,
            screen_param=str(data.get('screen_param', '')),
            cast_model=str(data.get('cast_model', '')),
            x_uid=str(data.get('x_uid', '')),
            cloud_guid=str(data.get('cloud_guid', '')),
            registered_at=float(data.get('registered_at', 0.0)),
            updated_at=float(data.get('updated_at', 0.0)))
    except (ValueError, TypeError, AttributeError):
        return default_device_state(), False
    if len(state.profile.android_id) != 16 or not state.profile.mac:
        return default_device_state(), False
    state.x_uid = compute_x_uid(state.profile)
    if not state.screen_param:
        state.screen_param = '7680-4320-280'
    if not state.cast_model:
        state.cast_model = state.profile.model
    return state, True


def save_device_state(path: str, state: DeviceState) -> None:
    tmp_path = path + f'.tmp.{os.getpid()}'
    try:
        parent = os.path.dirname(os.path.abspath(path))
        if parent:
            os.makedirs(parent, exist_ok=True)
        with open(tmp_path, 'w', encoding='utf-8') as f:
            f.write(json.dumps(dataclasses.asdict(state), indent=2, ensure_ascii=False, sort_keys=True) + '\n')
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_path, path)
    except OSError:
        with contextlib.suppress(OSError):
            if os.path.exists(tmp_path):
                os.remove(tmp_path)


def create_and_save_new_device(path: str) -> DeviceState:
    new_state = default_device_state()
    new_state.updated_at = now_f64()
    save_device_state(path, new_state)
    return new_state


# ---------------------------------------------------------------------------
# 请求头 / 报文构造
# ---------------------------------------------------------------------------


def build_identity(profile: DeviceProfile, app_channel: str, version: str) -> Identity:
    x_uid = compute_x_uid(profile)
    x_fingerprint, ts, _day0 = compute_fingerprint(x_uid, current_time_ms())
    headers = {
        'Accept': 'application/json',
        'Accept-Language': DEFAULT_ACCEPT_LANGUAGE,
        'Referer': 'api.cctv.cn',
        'User-Agent': 'cctv_app_tv',
        'UID': profile.android_id,
        'appChannel': app_channel,
        'X-Uid': x_uid,
        'X-Fingerprint': x_fingerprint,
        'X-Version': version,
        'Content-Type': 'application/json; charset=utf-8',
        'Connection': 'Keep-Alive',
        'Accept-Encoding': 'gzip',
        'Cache-Control': 'no-cache',
    }
    return Identity(x_uid=x_uid, x_fingerprint=x_fingerprint, fingerprint_timestamp_ms=ts, headers=headers)


def fresh_headers(template: dict, content_type: str, accept=None, force_ts=None) -> dict:
    headers = {}
    if accept is not None:
        headers['Accept'] = accept
    headers['X-Timestamp'] = str(force_ts if force_ts is not None else current_time_ms())
    headers['X-Nonce'] = str(uuid.uuid4())
    for key in ('Accept-Language', 'Referer', 'User-Agent', 'UID', 'appChannel', 'X-Uid', 'X-Fingerprint', 'X-Version'):
        if key in template:
            headers[key] = template[key]
    if content_type:
        headers['Content-Type'] = content_type
    for key in ('Connection', 'Accept-Encoding', 'Cache-Control'):
        if key in template:
            headers[key] = template[key]
    return headers


def compact_json_bytes(value, escape_forward_slashes: bool) -> bytes:
    text = json.dumps(value, separators=(',', ':'), ensure_ascii=False, sort_keys=True)
    if escape_forward_slashes:
        text = text.replace('/', '\\/')
    return text.encode('utf-8')


def normalize_aes_key(value: str) -> bytes:
    return (value.encode('utf-8') + b'\x00' * 32)[:32]


def aes_gcm_decrypt_b64(value: str, key: str) -> str:
    try:
        raw = base64.b64decode(value, validate=True)
    except (binascii.Error, ValueError) as e:
        raise YsptpError(f'base64 decode failed: {e}')
    if len(raw) <= 12:
        raise YsptpError('AES-GCM payload too short')
    try:
        plain = aes_gcm_decrypt(normalize_aes_key(key), raw[:12], raw[12:])
    except ValueError:
        raise YsptpError('AES-GCM decrypt failed')
    try:
        return plain.decode('utf-8')
    except UnicodeDecodeError as e:
        raise YsptpError(f'AES-GCM plaintext is not UTF-8: {e}')


def aes_gcm_encrypt_b64(value: str, key: str) -> str:
    nonce = secrets.token_bytes(12)
    encrypted = aes_gcm_encrypt(normalize_aes_key(key), nonce, value.encode('utf-8'))
    return base64.b64encode(nonce + encrypted).decode('ascii')


def rsa_encrypt_device_id(device_id: str) -> str:
    try:
        der = base64.b64decode(RSA_PUBLIC_KEY_B64, validate=True)
    except (binascii.Error, ValueError) as e:
        raise YsptpError(f'RSA public key base64 decode failed: {e}')
    n, e = parse_spki_rsa_pubkey(der)  # 只解析一次 DER (原版每个分块都重新解析)
    k = (n.bit_length() + 7) // 8
    hlen = 32
    chunk_size = k - 2 * hlen - 2
    out = bytearray()
    data = device_id.encode('utf-8')
    for i in range(0, len(data), chunk_size):
        out += rsa_oaep_sha256_encrypt(n, e, data[i:i + chunk_size], secrets.token_bytes(hlen))
    return base64.b64encode(bytes(out)).decode('ascii')


def report_model_from_build(profile: DeviceProfile) -> str:
    return profile.model.replace(profile.manufacturer, '').replace(' ', '')


def app_start_field(value, limit: int) -> str:
    return str(value)[:limit] if limit >= 0 else str(value)


def build_report_common_value(profile: DeviceProfile, x_uid: str, app_channel: str, version: str,
                              sdk_version: str, data_time_ms: int) -> dict:
    model = profile.report_model or report_model_from_build(profile)
    f = app_start_field
    return {
        'cctv_id': f(x_uid, 64), 'device_id': f(profile.android_id, 64), 'idfa': '', 'idfv': '',
        'user_id': '', 'app_key': f(REPORT_APP_KEY, 64), 'imei': '', 'android_id': f(profile.android_id, 64),
        'mac': f(profile.mac, 64), 'device_builder_type': f(profile.build_type, 64),
        'device_hardware': f(profile.hardware, 64), 'device_board': f(profile.board, 64),
        'device_brand': f(profile.brand, 64), 'device_params': f(profile.device, 64),
        'device_display': f(profile.display, 64), 'device_version_id': f(profile.version_id, 64),
        'device_host': f(profile.host, 128), 'device_product': f(profile.product, 64),
        'device_tags': f(profile.tags, 64), 'device_user': f(profile.user, 30),
        'device_fingerprint': f(profile.fingerprint, 128), 'device_manufacturer': f(profile.manufacturer, 64),
        'device_model': f(model, 50), 'device_resolution': f(profile.resolution, 20),
        'system_type': 'Android', 'device_type': 'TV', 'app_language': 'CHINESE',
        'app_version': f(version, 30), 'sdk_version': f(sdk_version, 30),
        'os_version': f(infer_os_version(profile), 20), 'app_channel': f(app_channel, 50),
        'data_time': f(data_time_ms, 13),
    }


def build_app_start_body(profile: DeviceProfile, x_uid: str, app_channel: str, version: str, data_time_ms: int) -> dict:
    return {'key': 'app_start_d1', 'value': build_report_common_value(profile, x_uid, app_channel, version, '', data_time_ms)}


def build_collect_headers(profile: DeviceProfile) -> dict:
    release = infer_os_version(profile)
    return {
        'Content-type': 'application/x-www-form-urlencoded',
        'Charset': 'UTF-8',
        'User-Agent': 'Dalvik/2.1.0 (Linux; U; Android ' + (release if release else 'Android')
                      + f'; {profile.model} Build/{profile.version_id})',
        'Connection': 'Keep-Alive',
        'Accept-Encoding': 'gzip',
    }


def parse_result_code(value):
    if isinstance(value, dict):
        for key in ('result', 'code', 'errCode', 'errcode', 'ret'):
            if key in value:
                raw = value[key]
                if isinstance(raw, bool):
                    continue
                if isinstance(raw, int):
                    return raw
                if isinstance(raw, str):
                    try:
                        return int(raw)
                    except ValueError:
                        pass
        for key in ('data', 'error', 'response'):
            if key in value:
                found = parse_result_code(value[key])
                if found is not None:
                    return found
    return None


def extract_guid(value) -> str:
    if isinstance(value, dict):
        data = value.get('data')
        if isinstance(data, dict):
            guid = data.get('guid')
            if isinstance(guid, str):
                return guid
    return ''


def root_headers(version: str) -> dict:
    return {
        'X-Uid': 'ROOT', 'X-Fingerprint': 'ROOT', 'X-Nonce': str(uuid.uuid4()),
        'X-Timestamp': str(current_time_ms()), 'X-Version': version, 'UID': 'ROOT',
        'Referer': 'api.cctv.cn', 'User-Agent': 'cctv_app_tv', 'appChannel': 'ROOT',
        'Connection': 'Keep-Alive', 'Accept-Encoding': 'gzip',
    }


def build_vdn_appcommon(version: str) -> str:
    return json.dumps({'adid': '', 'av': version, 'an': VDN_APP_NAME, 'ap': 'cctv_app_tv'},
                      separators=(',', ':'), ensure_ascii=False, sort_keys=True)


def url_host(url: str) -> str:
    try:
        return urllib.parse.urlsplit(url).hostname or ''
    except ValueError:
        return ''


def live_playback_host_needs_signed_headers(host: str) -> bool:
    lower = host.lower()
    return 'liveali' in lower or 'liveten' in lower


def default_cctv_playback_headers(uid: str) -> dict:
    return {'UID': uid, 'APPID': AK, 'Referer': 'api.cctv.cn', 'User-Agent': 'cctv_app_tv'}


def cctv_playback_headers_for_entry(entry: ChannelEntry) -> dict:
    headers = default_cctv_playback_headers(entry.android_id)
    for key in ('UID', 'APPID', 'APPRANDOMSTR', 'Referer', 'User-Agent', 'APPSIGN'):
        value = entry.playback_headers.get(key)
        if value:
            headers[key] = value
    return headers


def entry_missing_signed_playback_headers(entry: ChannelEntry) -> bool:
    host = entry.final_host or url_host(entry.final_url)
    if not live_playback_host_needs_signed_headers(host):
        return False
    return any(not entry.playback_headers.get(key, '').strip() for key in ('APPID', 'APPSIGN', 'APPRANDOMSTR'))


def ts_path_matches_final_url(ts_path: str, final_url: str) -> bool:
    try:
        prefix = urllib.parse.urlsplit(final_url).path
    except ValueError:
        return False
    if prefix.endswith('.m3u8'):
        prefix = prefix[:-len('.m3u8')]
    return bool(prefix) and ts_path.startswith(prefix)


def generate_app_random_str() -> str:
    return (f'{secrets.randbits(32):08x}-0000-{secrets.randbits(32) & 0xFFFF:04x}'
            f'-0000-00000000{secrets.randbits(32) & 0xFFFF:04x}')


def compute_vdn_code(app_secret: str, random_str=None):
    r = random_str if random_str is not None else generate_app_random_str()
    return md5_hex(f'{AK}{app_secret}{r}'), r


def is_ts_url(value: str) -> bool:
    try:
        return urllib.parse.urlsplit(value).path.lower().endswith('.ts')
    except ValueError:
        return False


def _rs_lines(text: str):
    norm = text.replace('\r\n', '\n')
    lines = norm.split('\n')
    if norm.endswith('\n'):
        lines.pop()
    return [ln[:-1] if ln.endswith('\r') else ln for ln in lines]


def rewrite_playlist_urls(text: str, base_url: str) -> str:
    try:
        parts = urllib.parse.urlsplit(base_url)
        has_base = bool(parts.scheme and parts.netloc)
    except ValueError:
        has_base = False
    out = []
    for line in _rs_lines(text):
        stripped = line.strip()
        if not stripped or stripped.startswith('#'):
            out.append(line)
        elif has_base:
            out.append(urllib.parse.urljoin(base_url, stripped))
        else:
            out.append(stripped)
    return ''.join(ln + '\n' for ln in out)


def header_value_clean(value: str) -> str:
    return value.replace('\r', '').replace('\n', '')


def form_urlencode_value(s: str) -> str:
    out = []
    for byte in s.encode('utf-8'):
        ch = chr(byte)
        if ch.isascii() and (ch.isalnum() or ch in '*-._'):
            out.append(ch)
        elif byte == 32:
            out.append('+')
        else:
            out.append(f'%{byte:02X}')
    return ''.join(out)


def form_encode(pairs) -> bytes:
    return '&'.join(f'{form_urlencode_value(k)}={form_urlencode_value(v)}' for k, v in pairs).encode('utf-8')


def _normalize_network_error(e: Exception) -> str:
    if isinstance(e, ConnectionRefusedError):
        return f'connection refused: {e}'
    if isinstance(e, ConnectionResetError):
        return f'connection reset by peer: {e}'
    if isinstance(e, (socket.timeout, TimeoutError)):
        return f'operation timed out: {e}'
    if isinstance(e, socket.gaierror):
        return f'failed to lookup address: {e}'
    if isinstance(e, urllib.error.URLError):
        reason = e.reason
        if isinstance(reason, Exception):
            return _normalize_network_error(reason)
        return f'network error: {e}'
    return f'network error: {e}'


# 共享 TLS 上下文: 原版每次 HTTPS 请求都 ssl.create_default_context() (要重新加载 CA 证书, 十几~几十毫秒)
_SSL_CTX = None
_SSL_CTX_LOCK = threading.Lock()


def default_ssl_context() -> ssl.SSLContext:
    global _SSL_CTX
    if _SSL_CTX is None:
        with _SSL_CTX_LOCK:
            if _SSL_CTX is None:
                _SSL_CTX = ssl.create_default_context()
    return _SSL_CTX


class HttpResponse:
    def __init__(self, status: int, reason: str, headers: dict, body: bytes):
        self.status = status
        self.reason = reason
        self.headers = headers
        self.body = body

    def text(self) -> str:
        return self.body.decode('utf-8', errors='replace')


class HttpClient:
    def __init__(self, timeout: float, insecure_tls: bool):
        self._timeout = max(timeout, 0.1)
        self._ctx = ssl._create_unverified_context() if insecure_tls else default_ssl_context()
        jar = http.cookiejar.CookieJar()
        self._opener = urllib.request.build_opener(
            urllib.request.ProxyHandler({}),
            urllib.request.HTTPCookieProcessor(jar),
            urllib.request.HTTPSHandler(context=self._ctx))
        self._jar = jar

    def _send(self, method: str, url: str, headers: dict, data: bytes | None) -> HttpResponse:
        req = urllib.request.Request(url, data=data, method=method)
        for k, v in headers.items():
            req.add_header(k, v)
        try:
            try:
                with self._opener.open(req, timeout=self._timeout) as resp:
                    status = resp.status
                    reason = resp.reason or ''
                    hdrs = {k.lower(): v for k, v in resp.headers.items()}
                    body = resp.read()
            except urllib.error.HTTPError as e:
                status = e.code
                reason = e.reason or ''
                try:
                    hdrs = {k.lower(): v for k, v in e.headers.items()} if e.headers else {}
                except Exception:
                    hdrs = {}
                try:
                    body = e.read()
                except Exception:
                    body = b''
        except Exception as e:
            raise YsptpError(_normalize_network_error(e))
        if 'gzip' in hdrs.get('content-encoding', '').lower():
            try:
                body = gzip.decompress(body)
            except (OSError, EOFError):
                pass
        return HttpResponse(status, reason, hdrs, body)

    def get(self, url: str, headers: dict) -> HttpResponse:
        return self._send('GET', url, headers, None)

    def post_bytes(self, url: str, headers: dict, data: bytes) -> HttpResponse:
        return self._send('POST', url, headers, data)

    def post_json(self, url: str, headers: dict, body) -> HttpResponse:
        data = json.dumps(body, separators=(',', ':'), ensure_ascii=False, sort_keys=True).encode('utf-8')
        return self._send('POST', url, headers, data)

    def post_form(self, url: str, headers: dict, pairs) -> HttpResponse:
        return self._send('POST', url, headers, form_encode(pairs))


def response_json(resp: HttpResponse):
    text = resp.text()
    try:
        value = json.loads(text)
    except ValueError:
        value = None
    return resp.status, text, value


def http_status_text(status: int, reason: str) -> str:
    return f'{status} {reason}'.strip() if reason else str(status)


# ---------------------------------------------------------------------------
# 解析器 (设备协议 → 高码率直播地址)
# ---------------------------------------------------------------------------

LINK_IDLE_TIMEOUT = 30.0
META_WRITE_MIN_INTERVAL = 5.0


@dataclasses.dataclass
class AppSession:
    profile: DeviceProfile
    identity: Identity
    client: HttpClient
    session_key: str
    cloud_guid: str
    version: str
    screen_param: str
    cast_model: str
    created_at: float
    generation: int
    last_heartbeat_at: float
    heartbeat_count: int
    last_heartbeat_result: str
    last_heartbeat_error: str
    linked_channels: set = dataclasses.field(default_factory=set)


class ResolverState:
    def __init__(self):
        self.cache: dict = {}
        self.playlist_cache: dict = {}
        self.channel_failures: dict = {}      # channel -> (failed_at, err_text, fail_count)
        self.generation = 0
        self.session_generation = 0
        self.sessions: dict = {}
        self.last_control_request_at = 0.0
        self.last_business_end_at = 0.0
        self.refreshing_channel = ''
        self.last_error = ''
        self.last_error_at = 0.0
        self.channel_last_access: dict = {}
        self.zap_channel = ''
        self.zap_time = 0.0
        self.zap_pending = ''
        self.zap_generation = 0
        self.last_device_wipe_at = 0.0
        self.device_wipe_day = ''
        self.device_wipe_count = 0

    @property
    def app_session(self):
        return self.sessions.get(0) or (next(iter(self.sessions.values())) if self.sessions else None)

    @app_session.setter
    def app_session(self, val):
        if val is not None:
            self.sessions[0] = val
        else:
            self.sessions.pop(0, None)


class Resolver:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.generic_client = HttpClient(args.timeout, args.insecure_tls)
        self.state = ResolverState()
        self.state_lock = threading.Lock()
        self.control_lock = threading.RLock()
        self.playlist_locks_lock = threading.Lock()
        self.playlist_locks: dict = {}
        self._meta_lock = threading.Lock()
        self._meta_last_write = 0.0
        self.state.cache = load_cache(args.meta_json)

    # ----- 后台线程 -----------------------------------------------------
    def start_heartbeat(self):
        def loop():
            while True:
                time.sleep(max(self.args.heartbeat_interval, 1.0))
                try:
                    self.send_heartbeat()
                except Exception:
                    pass

        threading.Thread(target=loop, daemon=True, name='heartbeat-keeper').start()

    # ----- 控制面限速 ---------------------------------------------------
    @contextlib.contextmanager
    def control_request_slot(self, _label: str):
        min_interval = max(0.0, float(self.args.refresh_interval))
        while True:
            with self.state_lock:
                last = self.state.last_control_request_at
                wait = 0.0 if last <= 0.0 else min_interval - (now_f64() - last)
            if wait <= 0.0:
                break
            time.sleep(wait)
        jitter = self.control_step_jitter_duration()
        if jitter is not None:
            time.sleep(jitter)
        try:
            yield
        finally:
            with self.state_lock:
                self.state.last_control_request_at = now_f64()

    def control_step_jitter_duration(self):
        min_ms = int(self.args.control_step_jitter_min_ms)
        max_ms = int(self.args.control_step_jitter_max_ms)
        if max_ms == 0:
            return None
        span = max(max_ms, min_ms) - min_ms
        extra = secrets.randbelow(span + 1) if span else 0
        return (min_ms + extra) / 1000.0

    # ----- 会话 ---------------------------------------------------------
    def app_session_fresh(self, sess: AppSession) -> bool:
        ttl = float(self.args.session_ttl)
        return ttl <= 0.0 or now_f64() - sess.created_at < ttl

    def app_session_ttl_remaining(self, sess: AppSession):
        ttl = float(self.args.session_ttl)
        if ttl <= 0.0:
            return None
        return ttl - (now_f64() - sess.created_at)

    def _session_usable(self, sess) -> bool:
        if sess is None or not self.app_session_fresh(sess):
            return False
        rem = self.app_session_ttl_remaining(sess)
        return rem is None or rem > 300.0

    def slot_device_json_path(self, slot: int) -> str:
        base = self.args.device_json
        if slot == 0:
            return base
        root, ext = os.path.splitext(base)
        return f'{root}-slot{slot}{ext}'

    def get_slot_for_channel(self, channel: str) -> int:
        return 0

    def ensure_slot_session(self, slot: int) -> AppSession:
        with self.state_lock:
            sess = self.state.sessions.get(slot)
        if self._session_usable(sess):
            return sess
        with self.control_lock:
            with self.state_lock:
                sess = self.state.sessions.get(slot)
                if self._session_usable(sess):
                    return sess
                self.state.session_generation += 1
                gen = self.state.session_generation
        sess = self.bootstrap_session(gen, device_json=self.slot_device_json_path(slot))
        with self.control_lock:
            with self.state_lock:
                cur = self.state.sessions.get(slot)
                if cur is None or not self.app_session_fresh(cur) or cur.generation < gen:
                    self.state.sessions[slot] = sess
                else:
                    sess = cur
        return sess

    def evict_idle_links(self, app_session, idle_sec=30.0):
        now = now_f64()
        with self.state_lock:
            last = dict(self.state.channel_last_access)
        for ch_slug in list(app_session.linked_channels):
            if now - last.get(ch_slug, 0.0) > idle_sec:
                app_session.linked_channels.discard(ch_slug)

    # ----- 换台防抖 -----------------------------------------------------
    def zap_debounced(self, channel: str) -> bool:
        if channel in TRUE_4K_CHANNELS:
            return False
        try:
            debounce = float(getattr(self.args, 'zap_debounce', 10.0))
        except (TypeError, ValueError):
            debounce = 10.0
        if debounce <= 0.0:
            return False
        now = now_f64()
        with self.state_lock:
            entry = self.state.cache.get(channel)
            if entry is not None and entry.fresh(now) and not entry_missing_signed_playback_headers(entry):
                return False
            if self.state.zap_channel != channel:
                self.state.zap_channel = channel
                self.state.zap_time = now
                self.state.zap_pending = ''
            if self.state.zap_pending == channel:
                return True
            if now - self.state.zap_time < debounce:
                self.state.zap_pending = channel
                self.state.zap_generation += 1
                gen = self.state.zap_generation
                delay = max(0.1, debounce - (now - self.state.zap_time))
                threading.Thread(target=self._zap_resolve_worker, args=(channel, gen, delay), daemon=True).start()
                return True
            return False

    def _zap_resolve_worker(self, channel: str, gen: int, delay: float):
        time.sleep(delay)
        with self.state_lock:
            if gen != self.state.zap_generation or self.state.zap_channel != channel:
                return
        try:
            self.ensure_channel(channel, force=True)
            log(f'[{channel}] 高码率后台预取完成, 继续停留将自动升级', min_interval=10.0)
        except Exception as e:
            log(f'[{channel}] 高码率后台预取失败: {e}, 继续 1080p', min_interval=10.0)
        finally:
            with self.state_lock:
                if self.state.zap_pending == channel:
                    self.state.zap_pending = ''

    # ----- 设备身份轮换 (与原版一致) -------------------------------------
    def rotate_device_on_400(self, reason: str) -> bool:
        now = now_f64()
        with self.state_lock:
            if now - self.state.last_device_wipe_at < 300.0:
                return False
            day = time.strftime('%Y-%m-%d', time.localtime(now))
            if self.state.device_wipe_day != day:
                self.state.device_wipe_day = day
                self.state.device_wipe_count = 0
            if self.state.device_wipe_count >= 5:
                log('[设备] 24小时内已自动换新身份 5 次，停止自动更换，请手动检查网络或设备', min_interval=60.0)
                return False
            self.state.last_device_wipe_at = now
            self.state.device_wipe_count += 1
            wipe_no = self.state.device_wipe_count
            target = self.slot_device_json_path(0)
            self.state.sessions.pop(0, None)
            self.state.cache.clear()
            self.state.playlist_cache.clear()
            self.state.channel_failures.clear()
            self.state.channel_last_access.clear()
        create_and_save_new_device(target)
        log(f'[设备] 检测到 400 ({reason})，旧身份已废弃，换新设备身份 (5分钟内仅一次，今日第 {wipe_no} 次)')
        return True

    # ----- 频道失败冷却 -------------------------------------------------
    def is_channel_in_cooldown(self, channel: str) -> bool:
        with self.state_lock:
            fail = self.state.channel_failures.get(channel)
        if fail is None:
            return False
        failed_at, _, fail_count = fail
        return (now_f64() - failed_at) < cooldown_for(fail_count)

    def get_channel_failure_info(self, channel: str):
        with self.state_lock:
            return self.state.channel_failures.get(channel)

    def clear_channel_cooldown(self, channel: str):
        with self.state_lock:
            self.state.channel_failures.pop(channel, None)

    def record_channel_failure(self, channel: str, err_text: str) -> int:
        now = now_f64()
        with self.state_lock:
            prev = self.state.channel_failures.get(channel)
            cnt = prev[2] + 1 if prev else 1
            self.state.channel_failures[channel] = (now, err_text, cnt)
            self.state.last_error = err_text
            self.state.last_error_at = now
            entry = self.state.cache.get(channel)
            if entry is not None:
                entry.last_refresh_error = err_text
                entry.last_refresh_failed_at = now
        return cnt

    def note_playlist_failure(self, channel: str, err: Exception) -> int:
        """播放列表获取失败后的统一善后: 丢弃缓存并记一次失败 (已记录过的不重复计数)。"""
        with self.state_lock:
            self.state.cache.pop(channel, None)
            self.state.playlist_cache.pop(channel, None)
        if getattr(err, 'failure_recorded', False):
            info = self.get_channel_failure_info(channel)
            return info[2] if info else 1
        return self.record_channel_failure(channel, str(err))

    # ----- 频道解析 -----------------------------------------------------
    def ensure_channel(self, channel: str, force: bool = False) -> ChannelEntry:
        if not force:
            now = now_f64()
            with self.state_lock:
                entry = self.state.cache.get(channel)
                if entry is not None and entry.fresh(now) and not entry_missing_signed_playback_headers(entry):
                    return entry
                fail = self.state.channel_failures.get(channel)
            if fail is not None:
                failed_at, err_msg, fail_count = fail
                cooldown = cooldown_for(fail_count)
                elapsed = now - failed_at
                if elapsed < cooldown:
                    err = YsptpError(f'channel {channel} in cooldown ({int(elapsed)}s/{int(cooldown)}s): {err_msg}')
                    err.failure_recorded = True
                    raise err
        with self.control_lock:
            if not force:
                now = now_f64()
                with self.state_lock:
                    entry = self.state.cache.get(channel)
                    if entry is not None and entry.fresh(now) and not entry_missing_signed_playback_headers(entry):
                        return entry
            try:
                entry = self.refresh_channel_controlled(channel)
            except YsptpError as err:
                err_text = str(err)
                if 'HTTP 400' in err_text and self.rotate_device_on_400(channel + ':' + err_text[:60]):
                    try:
                        entry = self.refresh_channel_controlled(channel)
                    except Exception:
                        pass
                    else:
                        self.write_meta()
                        return entry
                self.record_channel_failure(channel, err_text)
                self.write_meta()
                err.failure_recorded = True
                raise
            self.write_meta()
            return entry

    def refresh_channel_controlled(self, channel: str) -> ChannelEntry:
        with self.state_lock:
            wait = float(self.args.refresh_interval) - (now_f64() - self.state.last_business_end_at)
        if wait > 0.0:
            time.sleep(wait)
        with self.state_lock:
            self.state.refreshing_channel = channel
            self.state.generation += 1
            generation = self.state.generation
        log(f'[{channel}] 正在向央视频协议引擎请求直播源…', min_interval=10.0)
        try:
            slot = self.get_slot_for_channel(channel)
            limit = int(getattr(self.args, 'links_per_device', 6))
            app_session = self.ensure_slot_session(slot)
            if limit > 0 and channel not in app_session.linked_channels and len(app_session.linked_channels) >= limit:
                self.evict_idle_links(app_session, LINK_IDLE_TIMEOUT)
                if len(app_session.linked_channels) >= limit:
                    raise YsptpError(f'device link quota reached ({limit}), fallback to 1080p')
            live_id = channel_by_name(channel)
            if live_id is None:
                raise YsptpError(f'unknown channel {channel}')
            entry = self.resolve_channel_once(app_session, channel, live_id, generation)
            app_session.linked_channels.add(channel)
        finally:
            # 原版仅在 YsptpError 时复位, 其他异常会让 refreshing_channel 永久卡住
            with self.state_lock:
                self.state.last_business_end_at = now_f64()
                self.state.refreshing_channel = ''
        with self.state_lock:
            self.state.cache[channel] = entry
            self.state.playlist_cache.pop(channel, None)
            self.state.channel_failures.pop(channel, None)
            self.state.last_error = ''
        log(f'[{channel}] 直播源获取成功 (清晰度: {entry.rate_name or entry.rate or "高码率"})', min_interval=10.0)
        return entry

    def new_ytpaddr_client(self) -> HttpClient:
        return HttpClient(float(self.args.timeout), bool(self.args.insecure_tls))

    def bootstrap_session(self, generation: int, device_json: str = '') -> AppSession:
        target_json = device_json or self.args.device_json
        device_state, existed = load_device_state(target_json)
        if not existed or device_state.registered_at <= 0.0:
            device_state = default_device_state()
            device_state.updated_at = now_f64()
            save_device_state(target_json, device_state)
        profile = device_state.profile
        app_channel = 'dangbei'
        version = '1.4.1'
        identity = build_identity(profile, app_channel, version)
        device_state.x_uid = identity.x_uid
        client = self.new_ytpaddr_client()
        app_start = self.app_start_flow(client, profile, identity, app_channel, version)
        session_key = app_start.session_key
        try:
            cloud_guid = self.cloud_registration_flow(identity, identity.x_uid)
        except YsptpError as reg_err:
            raise YsptpError(f'cloud device registration failed: {reg_err}')
        if not cloud_guid and device_state.cloud_guid:
            cloud_guid = device_state.cloud_guid
        if not cloud_guid:
            raise YsptpError('cloud device registration failed: empty guid, fallback to 1080p')
        now = now_f64()
        device_state.x_uid = identity.x_uid
        device_state.updated_at = now
        device_state.cloud_guid = cloud_guid
        if device_state.registered_at <= 0.0:
            device_state.registered_at = now
        save_device_state(target_json, device_state)
        hb = self.heartbeat_flow(profile, identity, app_channel, version, cloud_guid)

        def _bg_telemetry():
            steps = (
                lambda: self.collect_report(profile, {
                    'key': 'app_start_d1',
                    'value': build_report_common_value(profile, identity.x_uid, app_channel, version,
                                                       COLLECT_SDK_VERSION, current_time_ms())}),
                lambda: self.dictionary_obtain(version),
                lambda: self.device_info_report_flow(profile, identity, app_channel, version, cloud_guid),
                lambda: self.index_flow(client, identity, app_channel),
                lambda: self.warmup_flow(client, identity, version),
            )
            for step in steps:
                try:
                    step()
                except Exception:
                    pass

        threading.Thread(target=_bg_telemetry, daemon=True, name='telemetry-worker').start()
        return AppSession(profile=profile, identity=identity, client=client, session_key=session_key,
                          cloud_guid=cloud_guid, version=version, screen_param=device_state.screen_param,
                          cast_model=device_state.cast_model, created_at=now_f64(), generation=generation,
                          last_heartbeat_at=now_f64(), heartbeat_count=1, last_heartbeat_result=hb,
                          last_heartbeat_error='')

    # ----- 控制面各步骤 -------------------------------------------------
    def collect_report(self, profile: DeviceProfile, body: dict) -> None:
        resp = self.generic_client.post_form(
            COLLECT_REPORT_URL, build_collect_headers(profile),
            [('info', json.dumps(body, separators=(',', ':'), ensure_ascii=False, sort_keys=True))])
        if not 200 <= resp.status < 300:
            raise YsptpError(f'collect report HTTP {http_status_text(resp.status, resp.reason)}')

    def dictionary_obtain(self, version: str) -> None:
        with self.control_request_slot('dictionary_obtain'):
            resp = self.generic_client.post_bytes(DICTIONARY_URL, root_headers(version), b'')
        if not 200 <= resp.status < 300:
            raise YsptpError(f'dictionary HTTP {http_status_text(resp.status, resp.reason)}')

    def app_start_flow(self, client: HttpClient, profile: DeviceProfile, identity: Identity,
                       app_channel: str, version: str) -> AppStartResult:
        last = ''
        for attempt in range(1, 3):
            if attempt > 1:
                time.sleep(float(attempt - 1))
            with self.control_request_slot('app_start'):
                token_time = current_time_ms()
                xfp, ts, _day0 = compute_fingerprint(identity.x_uid, token_time)
                identity.x_fingerprint = xfp
                identity.fingerprint_timestamp_ms = ts
                identity.headers['X-Fingerprint'] = xfp
                body = build_app_start_body(profile, identity.x_uid, app_channel, version, current_time_ms())
                payload = compact_json_bytes(body, True)
                headers = fresh_headers(identity.headers, 'application/json', 'application/json', ts)
                headers['UID'] = ''
                resp = client.post_bytes(APP_START_URL, headers, payload)
                status, text, value = response_json(resp)
                if 200 <= status < 300:
                    data = value.get('data') if isinstance(value, dict) else None
                    encrypted = ''
                    if isinstance(data, dict):
                        key_val = data.get('key', data)
                        encrypted = key_val if isinstance(key_val, str) else ''
                    elif isinstance(data, str):
                        encrypted = data
                    if encrypted:
                        return AppStartResult(session_key=aes_gcm_decrypt_b64(encrypted, xfp[:32]))
                last = f'app/start HTTP {status}: {text[:300]}'
        raise YsptpError(last)

    def cloud_registration_flow(self, identity: Identity, cloud_device_id: str) -> str:
        body = {'device_name': DEFAULT_DEVICE_NAME, 'device_id': rsa_encrypt_device_id(cloud_device_id)}

        def call(url, label):
            with self.control_request_slot(label):
                resp = self.generic_client.post_json(
                    url, fresh_headers(identity.headers, 'application/json', 'application/json', None), body)
            return response_json(resp)[2]

        value = call(CLOUD_GET_URL, 'cloud_get')
        result = parse_result_code(value)
        if result == RESULT_OK:
            return extract_guid(value)
        if result != RESULT_NEEDS_REGISTER and result != RESULT_GET_MISSING_OR_INVALID:
            return ''
        last_result = None
        guid = ''
        for _ in range(2):
            value = call(CLOUD_REGISTER_URL, 'cloud_register')
            last_result = parse_result_code(value)
            guid = extract_guid(value)
            if guid or last_result != RESULT_REGISTER_RETRY_LATER:
                break
        if guid:
            return guid
        if last_result in (RESULT_OK, RESULT_REGISTERED_ELSEWHERE, RESULT_GET_MISSING_OR_INVALID):
            return extract_guid(call(CLOUD_GET_URL, 'cloud_get_after_register'))
        return ''

    def device_info_report_flow(self, profile, identity, app_channel, version, cloud_guid) -> None:
        with self.control_request_slot('device_info_report'):
            value = build_report_common_value(profile, identity.x_uid, app_channel, version, '', current_time_ms())
            sdk_int = infer_sdk_int(profile)
            system_info = infer_os_version(profile)
            if sdk_int:
                system_info = sdk_int if not system_info else f'{system_info}/{sdk_int}'
            value.update({
                'version': version, 'network_status': 'WiFi', 'device_info': f'{profile.brand}-{profile.model}',
                'manufacturer': profile.manufacturer, 'cpu_info': '', 'chip_info': profile.hardware,
                'ram_info': '', 'memory_info': '', 'system_info': system_info, 'guid': cloud_guid,
            })
            resp = self.generic_client.post_json(
                REPORT_SINGLE_URL, fresh_headers(identity.headers, 'application/json', 'application/json', None),
                {'key': 'app_device_info', 'value': value})
            if not 200 <= resp.status < 300:
                raise YsptpError(f'device info HTTP {http_status_text(resp.status, resp.reason)}')

    def heartbeat_flow(self, profile, identity, app_channel, version, cloud_guid) -> str:
        with self.control_request_slot('heartbeat'):
            value = build_report_common_value(profile, identity.x_uid, app_channel, version, '', current_time_ms())
            value['network_type'] = 'WiFi'
            value['guid'] = cloud_guid
            value['other'] = ''
            resp = self.generic_client.post_json(
                REPORT_SINGLE_URL, fresh_headers(identity.headers, 'application/json', 'application/json', None),
                {'key': 'app_heartbeat', 'value': value})
            status, _text, parsed = response_json(resp)
            if not 200 <= status < 300:
                raise YsptpError(f'heartbeat HTTP {status}')
            code = parse_result_code(parsed)
            return '' if code is None else str(code)

    def index_flow(self, client, identity, app_channel) -> None:
        body = {'channel': app_channel, 'source': 'application'}
        with self.control_request_slot('index'):
            resp = client.post_json(INDEX_URL, fresh_headers(identity.headers, 'application/json', 'application/json', None), body)
            if not 200 <= resp.status < 300:
                raise YsptpError(f'index HTTP {http_status_text(resp.status, resp.reason)}')

    def warmup_flow(self, client, identity, version) -> None:
        appcommon = build_vdn_appcommon(version)
        with self.control_request_slot('drm_config'):
            resp = client.post_form(DRM_CONFIG_URL,
                                    fresh_headers(identity.headers, 'application/x-www-form-urlencoded', None, None),
                                    [('appcommon', appcommon)])
            if not 200 <= resp.status < 300:
                raise YsptpError(f'drm config HTTP {http_status_text(resp.status, resp.reason)}')
        url = f'{VERSION_CONFIG_URL}?appcommon={form_urlencode_value(appcommon)}'
        with self.control_request_slot('version_config'):
            headers = fresh_headers(identity.headers, '', None, None)
            headers.pop('Content-Type', None)
            resp = client.get(url, headers)
            if not 200 <= resp.status < 300:
                raise YsptpError(f'version config HTTP {http_status_text(resp.status, resp.reason)}')

    def resolve_channel_once(self, sess: AppSession, channel: str, live_id: str, generation: int) -> ChannelEntry:
        live01 = self.live_v1_01_flow(sess, live_id, channel)
        app_secret = self.live_v1_02_flow(sess)
        vdn = self.vdn_getstream_flow(sess.identity, sess.version, live01.live_url, app_secret)
        now = now_f64()
        playback_headers = default_cctv_playback_headers(sess.profile.android_id)
        playback_headers['APPRANDOMSTR'] = vdn.app_random_str
        playback_headers['APPSIGN'] = vdn.app_sign
        sess.linked_channels.add(channel)
        return ChannelEntry(
            channel=channel, live_id=live_id, final_url=vdn.final_url, playback_headers=playback_headers,
            android_id=sess.profile.android_id, x_uid=sess.identity.x_uid, rate=live01.rate,
            rate_name=live01.rate_name or '高码率', raw_live_host=url_host(live01.live_url),
            final_host=url_host(vdn.final_url), refreshed_at=now, expires_at=now + float(self.args.cache_ttl),
            generation=generation, last_refresh_error='', last_refresh_failed_at=0.0,
            session_generation=sess.generation)

    def live_v1_01_flow(self, sess: AppSession, live_id: str, channel: str = '') -> Live01Result:
        body = {'screenParam': sess.screen_param, 'rate': '', 'systemType': 'ios', 'model': sess.cast_model,
                'id': live_id, 'userId': DEFAULT_LIVE_USER_ID, 'clientSign': 'cctvVideo',
                'deviceId': {'serial': '', 'imei': '', 'android_id': ''}}
        with self.control_request_slot('live_v1_01'):
            resp = sess.client.post_json(
                LIVE_V1_01_URL, fresh_headers(sess.identity.headers, 'application/json', 'application/json', None), body)
        status, text, value = response_json(resp)
        if not 200 <= status < 300:
            raise YsptpError(f'live/v1/01 HTTP {status}: {text[:300]}')
        videos = None
        if isinstance(value, dict):
            data = value.get('data')
            if isinstance(data, dict):
                videos = data.get('videoList') or data.get('videos')
        if not isinstance(videos, list):
            raise YsptpError('live/v1/01 missing videos')
        selected = None
        fallback = None
        for item in videos:
            if not isinstance(item, dict):
                continue
            url = item.get('url')
            if not isinstance(url, str) or not url:
                continue
            if fallback is None:
                fallback = item
            if channel != 'cctv6' and item.get('rate') == '36p':
                selected = item
                break
        video = selected if selected is not None else fallback
        if video is None:
            raise YsptpError('live/v1/01 no usable URL')
        raw_url = video.get('url', '')
        if raw_url.startswith('http://') or raw_url.startswith('https://'):
            live_url = raw_url
        else:
            live_url = aes_gcm_decrypt_b64(raw_url, sess.session_key)
        rate = video.get('rate')
        rate_name = video.get('rateName')
        return Live01Result(live_url=live_url, rate=rate if isinstance(rate, str) else '',
                            rate_name=rate_name if isinstance(rate_name, str) else '')

    def live_v1_02_flow(self, sess: AppSession) -> str:
        with self.control_request_slot('live_v1_02'):
            body = {'guid': aes_gcm_encrypt_b64('', sess.session_key)}
            resp = sess.client.post_json(
                LIVE_V1_02_URL, fresh_headers(sess.identity.headers, 'application/json', 'application/json', None), body)
        status, text, value = response_json(resp)
        if not 200 <= status < 300:
            raise YsptpError(f'live/v1/02 HTTP {status}: {text[:300]}')
        encrypted = None
        if isinstance(value, dict):
            data = value.get('data')
            if isinstance(data, dict):
                for key in ('appSecret', 'app_secret'):
                    v = data.get(key)
                    if isinstance(v, str):
                        encrypted = v
                        break
            if encrypted is None and isinstance(data, str):
                encrypted = data
        if encrypted is None:
            raise YsptpError('live/v1/02 missing appSecret')
        return aes_gcm_decrypt_b64(encrypted, sess.session_key)

    def vdn_getstream_flow(self, identity: Identity, version: str, live_url: str, app_secret: str) -> VdnGetStreamResult:
        with self.control_request_slot('vdn_getstream'):
            app_sign, random_str = compute_vdn_code(app_secret, None)
            headers = fresh_headers(identity.headers, 'application/x-www-form-urlencoded', None, None)
            headers['APPID'] = AK
            headers['APPSIGN'] = app_sign
            headers['APPRANDOMSTR'] = random_str
            resp = self.generic_client.post_form(
                VDN_GETSTREAM_URL, headers, [('appcommon', build_vdn_appcommon(version)), ('url', live_url)])
        status, text, value = response_json(resp)
        if not 200 <= status < 300:
            raise YsptpError(f'VDN HTTP {status}: {text[:300]}')
        if isinstance(value, dict):
            succeed = value.get('succeed')
            if isinstance(succeed, str):
                succeed_str = succeed.strip('"')
            elif succeed is not None:
                succeed_str = json.dumps(succeed, separators=(',', ':'), ensure_ascii=False).strip('"')
            else:
                succeed_str = ''
            if succeed_str == '1':
                url = value.get('url')
                if isinstance(url, str):
                    return VdnGetStreamResult(final_url=url, app_sign=app_sign, app_random_str=random_str)
        raise YsptpError(f'VDN did not return final URL: {text[:400]}')

    def send_heartbeat(self) -> None:
        if not self.control_lock.acquire(blocking=False):
            return
        try:
            with self.state_lock:
                slots = list(self.state.sessions.keys())
            if not slots:
                return
            for slot in slots:
                try:
                    with self.state_lock:
                        s_curr = self.state.sessions.get(slot)
                    if s_curr is None:
                        continue
                    if not self._session_usable(s_curr):
                        s_curr = self.ensure_slot_session(slot)
                    with self.state_lock:
                        wait = float(self.args.refresh_interval) - (now_f64() - self.state.last_business_end_at)
                    if wait > 0.0:
                        time.sleep(wait)
                    code = self.heartbeat_flow(s_curr.profile, s_curr.identity, 'dangbei', s_curr.version, s_curr.cloud_guid)
                    with self.state_lock:
                        self.state.last_business_end_at = now_f64()
                        s_curr.last_heartbeat_at = now_f64()
                        s_curr.heartbeat_count += 1
                        s_curr.last_heartbeat_result = code
                        s_curr.last_heartbeat_error = ''
                except YsptpError as err:
                    err_text = str(err)
                    with self.state_lock:
                        s_curr = self.state.sessions.get(slot)
                        if s_curr is not None:
                            s_curr.last_heartbeat_error = err_text
                        self.state.last_error = f'heartbeat failed on slot {slot}: {err_text}'
                        self.state.last_error_at = now_f64()
                except Exception:
                    pass
            set_resolver_ready(True)
        finally:
            self.control_lock.release()

    # ----- 播放列表 / 分片代理 -------------------------------------------
    def proxy_playlist_ts_urls(self, playlist: str, proxy_origin: str, proxy_prefix=None) -> str:
        origin = (proxy_prefix or proxy_origin).rstrip('/')
        proxy_query = '/proxy?ts=' if proxy_prefix is not None else '/proxy.ts?='
        out = []
        for line in _rs_lines(playlist):
            stripped = line.strip()
            if stripped and not stripped.startswith('#') and is_ts_url(stripped):
                out.append(f'{origin}{proxy_query}{encode_proxy_token(stripped)}')
            else:
                out.append(line)
        return ''.join(ln + '\n' for ln in out)

    def playback_headers_for_ts_url(self, real_url: str) -> dict:
        try:
            parsed = urllib.parse.urlsplit(real_url)
        except ValueError as e:
            raise YsptpError(f'invalid proxy ts URL: {e}')
        host = parsed.hostname
        if not host:
            raise YsptpError('proxy ts URL missing host')
        ts_path = parsed.path
        same_host_headers = None
        with self.state_lock:
            for entry in self.state.cache.values():
                if entry_missing_signed_playback_headers(entry):
                    continue
                entry_host = entry.final_host or url_host(entry.final_url)
                if entry_host.lower() != host.lower():
                    continue
                headers = cctv_playback_headers_for_entry(entry)
                if ts_path_matches_final_url(ts_path, entry.final_url):
                    return headers
                if same_host_headers is None:
                    same_host_headers = headers
        if same_host_headers is not None:
            return same_host_headers
        if live_playback_host_needs_signed_headers(host):
            raise YsptpError(f'missing cached signed playback headers for {host}')
        return default_cctv_playback_headers(current_cctv_android_id(self))

    def fetch_playlist(self, entry: ChannelEntry, proxy_origin: str, proxy_prefix=None):
        now = now_f64()
        with self.state_lock:
            probe = inspect_playlist_cache(self.state.playlist_cache.get(entry.channel), entry, proxy_origin, proxy_prefix, now)
            if probe.state == 'hit':
                cached = self.state.playlist_cache[entry.channel]
                return cached.body, cached.content_type, probe
        with self.playlist_locks_lock:
            lock = self.playlist_locks.get(entry.channel)
            if lock is None:
                lock = self.playlist_locks[entry.channel] = threading.Lock()
        with lock:
            now = now_f64()
            with self.state_lock:
                probe = inspect_playlist_cache(self.state.playlist_cache.get(entry.channel), entry, proxy_origin, proxy_prefix, now)
                if probe.state == 'hit':
                    cached = self.state.playlist_cache[entry.channel]
                    return cached.body, cached.content_type, probe
                miss_probe = probe
            playback_headers = cctv_playback_headers_for_entry(entry)

            def recent_cached():
                with self.state_lock:
                    cached = self.state.playlist_cache.get(entry.channel)
                if cached and now_f64() - cached.cached_at < 20.0:
                    return cached.body, cached.content_type, miss_probe
                return None

            try:
                status, content_type, text = fetch_playlist_http(entry.final_url, playback_headers)
            except YsptpError:
                fallback = recent_cached()
                if fallback:
                    return fallback
                raise
            if not 200 <= status < 300:
                fallback = recent_cached()
                if fallback:
                    return fallback
                raise YsptpError(f'upstream m3u8 HTTP {status}: {text[:300]}')
            body = rewrite_playlist_urls(text, entry.final_url)
            body = self.proxy_playlist_ts_urls(body, proxy_origin, proxy_prefix)
            if float(self.args.playlist_cache_ttl) > 0.0:
                now = now_f64()
                cached = PlaylistCacheEntry(
                    body=body, content_type=content_type, cached_at=now,
                    expires_at=now + float(self.args.playlist_cache_ttl), final_url=entry.final_url,
                    android_id=entry.android_id, proxy_origin=proxy_origin, proxy_prefix=proxy_prefix or '')
                with self.state_lock:
                    self.state.playlist_cache[entry.channel] = cached
            return body, content_type, miss_probe

    def fetch_channel_playlist(self, channel: str, host_header: str, scheme: str = 'http'):
        with self.state_lock:
            self.state.channel_last_access[channel] = now_f64()
        if self.zap_debounced(channel):
            log(f'[{channel}] 换台防抖: 先出 1080p, 停留后自动升码率', min_interval=10.0)
            return None
        host = host_header.strip() if host_header else f'localhost:{server_port}'
        proxy_origin = f'{scheme}://{host}'
        entry = self.ensure_channel(channel)
        for attempt in range(2):
            try:
                body, _content_type, _probe = self.fetch_playlist(entry, proxy_origin)
                self.clear_channel_cooldown(channel)
                return body
            except YsptpError as e:
                err_str = str(e)
                is_expiry = any(s in err_str for s in ('HTTP 403', 'HTTP 404', 'HTTP 401', 'upstream m3u8'))
                if is_expiry and attempt == 0:
                    log(f'[{channel}] 高码率播放地址已过期，正在极速重取新地址…', min_interval=4.0)
                    with self.state_lock:
                        self.state.cache.pop(channel, None)
                        self.state.playlist_cache.pop(channel, None)
                    entry = self.ensure_channel(channel, force=True)
                    continue
                raise

    # ----- 状态 / 持久化 ------------------------------------------------
    def status_json(self) -> dict:
        with self.state_lock:
            cache_snap = dict(self.state.cache)
            playlist_snap = dict(self.state.playlist_cache)
            sess = self.state.app_session
            refreshing = self.state.refreshing_channel
            last_business_end_at = self.state.last_business_end_at
            last_error = self.state.last_error
            generation = self.state.generation
            session_generation = self.state.session_generation
        now = now_f64()
        a = self.args
        if os.path.exists(a.device_json):
            loaded, existed = load_device_state(a.device_json)
            device_state = {
                'exists': existed, 'android_id': loaded.profile.android_id, 'mac': loaded.profile.mac,
                'brand': loaded.profile.brand, 'model': loaded.profile.model, 'screen_param': loaded.screen_param,
                'x_uid': loaded.x_uid, 'cloud_guid_present': bool(loaded.cloud_guid),
                'registered_at': loaded.registered_at, 'updated_at': loaded.updated_at}
        else:
            device_state = {'exists': False}
        cache = {
            k: {'live_id': v.live_id, 'fresh': v.fresh(now),
                'age_seconds': rust_round((now - v.refreshed_at) * 1000.0) / 1000.0,
                'expires_in_seconds': rust_round((v.expires_at - now) * 1000.0) / 1000.0,
                'rate': v.rate, 'rate_name': v.rate_name, 'final_host': v.final_host,
                'generation': v.generation, 'session_generation': v.session_generation,
                'last_refresh_error': v.last_refresh_error}
            for k, v in cache_snap.items()}
        playlist_cache = {
            k: {'fresh': now < v.expires_at, 'age_seconds': rust_round((now - v.cached_at) * 1000.0) / 1000.0,
                'expires_in_seconds': rust_round((v.expires_at - now) * 1000.0) / 1000.0,
                'bytes': len(v.body.encode('utf-8')), 'content_type': v.content_type,
                'proxy_origin': v.proxy_origin, 'proxy_prefix': v.proxy_prefix}
            for k, v in playlist_snap.items()}
        if sess is not None:
            ttl = float(a.session_ttl)
            app_session = {
                'active': True, 'generation': sess.generation,
                'age_seconds': rust_round((now - sess.created_at) * 1000.0) / 1000.0,
                'fresh': self.app_session_fresh(sess),
                'expires_in_seconds': ttl - (now - sess.created_at) if ttl > 0.0 else None,
                'android_id': sess.profile.android_id, 'mac': sess.profile.mac, 'brand': sess.profile.brand,
                'model': sess.profile.model, 'screen_param': sess.screen_param, 'cast_model': sess.cast_model,
                'x_uid': sess.identity.x_uid, 'cloud_guid_present': bool(sess.cloud_guid),
                'fingerprint_timestamp_ms': sess.identity.fingerprint_timestamp_ms,
                'heartbeat_count': sess.heartbeat_count,
                'last_heartbeat_age_seconds': rust_round((now - sess.last_heartbeat_at) * 1000.0) / 1000.0,
                'last_heartbeat_result': sess.last_heartbeat_result, 'last_heartbeat_error': sess.last_heartbeat_error}
        else:
            app_session = {'active': False, 'generation': session_generation}
        return {
            'channels': [c for c, _ in channels()],
            'cache_ttl_seconds': float(a.cache_ttl),
            'playlist_cache_ttl_seconds': float(a.playlist_cache_ttl),
            'refresh_interval_seconds': float(a.refresh_interval),
            'control_step_jitter_min_ms': int(a.control_step_jitter_min_ms),
            'control_step_jitter_max_ms': int(a.control_step_jitter_max_ms),
            'heartbeat_interval_seconds': float(a.heartbeat_interval),
            'session_ttl_seconds': float(a.session_ttl),
            'meta_json': a.meta_json, 'device_json': a.device_json, 'device_state': device_state,
            'refreshing_channel': refreshing, 'generation': generation, 'app_session': app_session,
            'last_business_end_at': last_business_end_at, 'last_error': last_error,
            'device_profile_pool_size': len(DEVICE_PROFILE_POOL), 'cache': cache, 'playlist_cache': playlist_cache,
        }

    def write_meta(self, force: bool = False) -> None:
        """写 meta 状态文件。

        原版 status_json() 引用了从未初始化的 self.http_queue, 每次都抛 AttributeError,
        而调用方又只捕获 OSError 或整体吞掉异常 —— 结果是 meta 文件从未真正写成功。
        这里修复该问题, 并做 5 秒节流、去掉 fsync、整体异常隔离 (meta 仅用于诊断/热启动)。
        """
        now = now_f64()
        with self._meta_lock:
            if not force and now - self._meta_last_write < META_WRITE_MIN_INTERVAL:
                return
            self._meta_last_write = now
        tmp_path = ''
        try:
            payload = self.status_json()
            with self.state_lock:
                payload['cache_detail'] = {k: dataclasses.asdict(v) for k, v in self.state.cache.items()}
            payload['session_detail_note'] = 'Session secrets are intentionally not persisted for reuse; Python process keeps live session in memory only.'
            payload['device_state_note'] = 'Randomized TV device identity is persisted in device-state-rs.json after cloud registration succeeds; a new identity reset creates a new profile and MAC.'
            parent = os.path.dirname(os.path.abspath(self.args.meta_json))
            if parent:
                os.makedirs(parent, exist_ok=True)
            tmp_path = self.args.meta_json + f'.tmp.{os.getpid()}'
            with open(tmp_path, 'w', encoding='utf-8') as f:
                f.write(json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True) + '\n')
            os.replace(tmp_path, self.args.meta_json)
        except Exception:
            with contextlib.suppress(OSError):
                if tmp_path and os.path.exists(tmp_path):
                    os.remove(tmp_path)


def load_cache(path: str) -> dict:
    try:
        with open(path, encoding='utf-8') as f:
            value = json.load(f)
    except (OSError, ValueError):
        return {}
    detail = value.get('cache_detail') if isinstance(value, dict) else None
    if not isinstance(detail, dict):
        return {}
    try:
        return {k: ChannelEntry.from_dict(v) for k, v in detail.items() if isinstance(v, dict)}
    except (ValueError, TypeError):
        return {}


# ---------------------------------------------------------------------------
# 上游请求 (http/https 通用)
# ---------------------------------------------------------------------------


def _playback_request_headers(playback_headers: dict, extra: dict | None = None) -> dict:
    headers = {}
    for key in ('UID', 'APPID', 'APPRANDOMSTR', 'Referer', 'User-Agent', 'APPSIGN'):
        value = playback_headers.get(key)
        if value is not None and str(value).strip():
            headers[key] = header_value_clean(str(value))
    headers['Accept'] = '*/*'
    headers['Accept-Encoding'] = 'identity'
    headers['Connection'] = 'close'
    if extra:
        headers.update(extra)
    return headers


def open_upstream(url: str, headers: dict, method: str = 'GET', timeout: float = 30.0):
    """发起上游请求并返回 (conn, resp); 调用方负责 conn.close()。"""
    try:
        parts = urllib.parse.urlsplit(url)
        port = parts.port
    except ValueError as e:
        raise YsptpError(f'invalid upstream URL: {e}')
    if parts.scheme not in ('http', 'https'):
        raise YsptpError(f'unsupported upstream scheme: {parts.scheme}')
    host = parts.hostname
    if not host:
        raise YsptpError('upstream URL missing host')
    is_https = parts.scheme == 'https'
    target = parts.path or '/'
    if parts.query:
        target += '?' + parts.query
    req_headers = dict(headers)
    req_headers['Host'] = f'{host}:{port}' if port else host
    if is_https:
        conn = http.client.HTTPSConnection(host, port or 443, timeout=timeout, context=default_ssl_context())
    else:
        conn = http.client.HTTPConnection(host, port or 80, timeout=timeout)
    try:
        conn.request(method, target, headers=req_headers)
        resp = conn.getresponse()
    except Exception as e:
        conn.close()
        raise YsptpError(_normalize_network_error(e))
    return conn, resp


def fetch_playlist_http(final_url: str, playback_headers: dict):
    conn, resp = open_upstream(final_url, _playback_request_headers(playback_headers))
    try:
        status = resp.status
        content_type = resp.getheader('Content-Type') or 'application/vnd.apple.mpegurl'
        try:
            body = resp.read()
        except Exception as e:
            raise YsptpError(_normalize_network_error(e))
    finally:
        conn.close()
    return status, content_type, body.decode('utf-8', errors='replace')


# ---------------------------------------------------------------------------
# 代理令牌 (HMAC 签名)
# 原版 /proxy.ts 与 /engine_proxy 接受任意 URL, 默认绑定 0.0.0.0 时等于开放代理 / SSRF。
# 现在播放列表里下发的 URL 都带签名, 只有本进程签发过的 URL 才会被代理。
# ---------------------------------------------------------------------------

_PROXY_SECRET = secrets.token_hex(32).encode('ascii')


def init_proxy_secret(data_dir: str) -> None:
    """优先复用数据目录里持久化的密钥, 这样重启后播放器手里的旧链接仍然有效。"""
    global _PROXY_SECRET
    path = os.path.join(data_dir, '.proxy-secret')
    try:
        with open(path, 'rb') as f:
            raw = f.read().strip()
        if len(raw) >= 32:
            _PROXY_SECRET = raw
            return
    except OSError:
        pass
    secret = secrets.token_hex(32).encode('ascii')
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, 'wb') as f:
            f.write(secret)
    except OSError:
        pass
    _PROXY_SECRET = secret


def sign_value(value: str) -> str:
    return _hmac.new(_PROXY_SECRET, value.encode('utf-8'), hashlib.sha256).hexdigest()[:24]


def verify_signature(value: str, sig: str) -> bool:
    return bool(sig) and _hmac.compare_digest(sig, sign_value(value))


def encode_proxy_token(url: str) -> str:
    body = base64.urlsafe_b64encode(url.encode('utf-8')).rstrip(b'=').decode('ascii')
    return f'{body}.{sign_value(url)}'


def query_param(url: str, name: str):
    if '?' not in url:
        return None
    _, query = url.split('?', 1)
    for pair in query.split('&'):
        key, _, value = pair.partition('=')
        if key == name:
            return value
    return None


def proxy_ts_token(url: str):
    if '?' not in url:
        return None
    _, query = url.split('?', 1)
    if query.startswith('='):
        return query[1:] or None
    token = query_param(url, 'ts') or query_param(url, 'url')
    if token:
        return token
    if query and '=' not in query:
        return query
    return None


def decode_proxy_ts_url(token: str) -> str:
    body, _, sig = token.rpartition('.')
    if not body or not sig:
        raise YsptpError('invalid proxy ts token: missing signature')
    padded = body + '=' * (-len(body) % 4)
    try:
        raw = base64.urlsafe_b64decode(padded.encode('ascii'))
    except (binascii.Error, ValueError) as e:
        raise YsptpError(f'invalid proxy ts token: {e}')
    try:
        value = raw.decode('utf-8')
    except UnicodeDecodeError as e:
        raise YsptpError(f'proxy ts token is not UTF-8: {e}')
    if not verify_signature(value, sig):
        raise YsptpError('invalid proxy ts token: bad signature')
    try:
        parsed = urllib.parse.urlsplit(value)
    except ValueError as e:
        raise YsptpError(f'proxy ts token is not a URL: {e}')
    if parsed.scheme not in ('http', 'https'):
        raise YsptpError(f'proxy ts currently requires http or https URL, got {parsed.scheme}')
    if not parsed.path.lower().endswith('.ts'):
        raise YsptpError('proxy ts URL is not a .ts segment')
    return value


def current_cctv_android_id(resolver: Resolver) -> str:
    if os.path.exists(resolver.args.device_json):
        loaded, _ = load_device_state(resolver.args.device_json)
        if loaded.profile.android_id:
            return loaded.profile.android_id
    with resolver.state_lock:
        sess = resolver.state.app_session
        if sess is not None and sess.profile.android_id:
            return sess.profile.android_id
        for entry in resolver.state.cache.values():
            if entry.android_id:
                return entry.android_id
    raise YsptpError('missing cctv android_id')


def resolve_paths(args: argparse.Namespace) -> None:
    d = binary_dir()
    if not args.meta_json.strip():
        args.meta_json = os.path.join(d, 'proxy-cache-state-rs.json')
    if not args.device_json.strip():
        args.device_json = os.path.join(d, 'device-state-rs.json')


# ---------------------------------------------------------------------------
# JCE 编解码 / 时移 (1080p 备用通道)
# ---------------------------------------------------------------------------


class W:
    def __init__(self):
        self.b = bytearray()

    def head(self, typ, tag):
        if tag < 15:
            self.b.append(((tag & 15) << 4) | (typ & 15))
        else:
            self.b.append(240 | (typ & 15))
            self.b.append(tag)

    def byte(self, v, tag):
        v = int(v)
        if v == 0:
            self.head(12, tag)
        else:
            self.head(0, tag)
            self.b += struct.pack('>b', v)

    def short(self, v, tag):
        v = int(v)
        if -128 <= v <= 127:
            self.byte(v, tag)
        else:
            self.head(1, tag)
            self.b += struct.pack('>h', v)

    def int(self, v, tag):
        v = int(v)
        if -32768 <= v <= 32767:
            self.short(v, tag)
        else:
            self.head(2, tag)
            self.b += struct.pack('>i', v)

    def long(self, v, tag):
        v = int(v)
        if -2147483648 <= v <= 2147483647:
            self.int(v, tag)
        else:
            self.head(3, tag)
            self.b += struct.pack('>q', v)

    def float(self, v, tag):
        self.head(4, tag)
        self.b += struct.pack('>f', float(v))

    def double(self, v, tag):
        self.head(5, tag)
        self.b += struct.pack('>d', float(v))

    def string(self, s, tag):
        if s is None:
            return
        data = str(s).encode('utf-8')
        if len(data) > 255:
            self.head(7, tag)
            self.b += struct.pack('>i', len(data))
        else:
            self.head(6, tag)
            self.b.append(len(data))
        self.b += data

    def bytes(self, data, tag):
        data = bytes(data)
        self.head(13, tag)
        self.head(0, 0)
        self.int(len(data), 0)
        self.b += data

    def struct(self, fn, tag):
        self.head(10, tag)
        fn(self)
        self.head(11, 0)

    def list(self, items, tag, wf):
        self.head(9, tag)
        self.int(len(items), 0)

    def out(self):
        return bytes(self.b)


class R:
    def __init__(self, data):
        self.d = memoryview(data)
        self.p = 0

    def rem(self):
        return len(self.d) - self.p

    def get(self, n):
        if self.p + n > len(self.d):
            raise EOFError
        b = self.d[self.p:self.p + n].tobytes()
        self.p += n
        return b

    def u8(self):
        return self.get(1)[0]

    def head(self):
        b = self.u8()
        typ = b & 15
        tag = (b & 240) >> 4
        if tag == 15:
            tag = self.u8()
        return typ, tag

    def value(self, typ):
        if typ == 0:
            return struct.unpack('>b', self.get(1))[0]
        if typ == 1:
            return struct.unpack('>h', self.get(2))[0]
        if typ == 2:
            return struct.unpack('>i', self.get(4))[0]
        if typ == 3:
            return struct.unpack('>q', self.get(8))[0]
        if typ == 4:
            return struct.unpack('>f', self.get(4))[0]
        if typ == 5:
            return struct.unpack('>d', self.get(8))[0]
        if typ == 6:
            n = self.u8()
            return self.get(n).decode('utf-8', 'replace')
        if typ == 7:
            n = struct.unpack('>i', self.get(4))[0]
            return self.get(n).decode('utf-8', 'replace')
        if typ == 8:
            n = self._int()
            return {self._fv(): self._fv() for _ in range(n)}
        if typ == 9:
            n = self._int()
            return [self._fv() for _ in range(n)]
        if typ == 10:
            return self.struct()
        if typ == 11:
            return None
        if typ == 12:
            return 0
        if typ == 13:
            self.head()
            n = self._int()
            return self.get(n)
        raise ValueError('type %d' % typ)

    def _fv(self):
        t, _ = self.head()
        return self.value(t)

    def _int(self):
        t, _ = self.head()
        return int(self.value(t))

    def struct(self):
        m = {}
        while self.rem() > 0:
            t, tag = self.head()
            if t == 11:
                break
            m[tag] = self.value(t)
        return m


VER_NAME, VER_CODE = '3.2.7.26212', '302070'
APP_ID, QMF_APP_ID, QMF_PLATFORM, BIZ_ID = '1200013', 10012, 1, 0
CHAN_ID = '10070'
GUID = ''.join(random.choice('0123456789abcdef') for _ in range(32))


def _qua(w):
    w.string(VER_NAME, 0)
    w.string(VER_CODE, 1)
    w.int(1080, 2)
    w.int(2400, 3)
    w.int(3, 4)
    w.string('12', 5)
    w.int(1, 6)
    w.int(1, 7)
    w.int(420, 8)
    w.string(CHAN_ID, 9)
    for i in range(10, 15):
        w.string('', i)
    w.struct(lambda ww: (ww.int(0, 0), ww.byte(0, 1), ww.string('', 2)), 15)
    w.string('', 16)
    w.string('', 17)
    w.string('', 18)
    w.struct(lambda ww: (ww.int(0, 0), ww.float(0, 1), ww.float(0, 2), ww.double(0, 3)), 19)
    w.string(GUID[:16], 20)
    w.string('Pixel 6', 21)
    w.int(1, 22)
    for i in range(23, 27):
        w.int(0, i)
    w.string('', 27)
    w.string('', 28)
    w.string(GUID, 29)


def _head(w, cmd, reqid):
    w.int(reqid, 0)
    w.int(cmd, 1)
    w.struct(lambda ww: _qua(ww), 2)
    w.string(APP_ID, 3)
    w.string(GUID, 4)
    w.list([], 5, None)
    w.struct(lambda ww: None, 6)
    w.list([], 7, None)
    w.int(0, 8)
    w.int(0, 9)
    w.int(0, 10)


def _wrap(cmd, body, reqid):
    w = W()
    w.struct(lambda ww: _head(ww, cmd, reqid), 0)
    w.bytes(body, 1)
    reqcmd = w.out()
    inner = bytearray([38]) + struct.pack('>i', len(reqcmd) + 17) + bytes([1]) + b'\x00' * 10 + reqcmd + bytes([40])
    comp = gzip.compress(bytes(inner))
    out = bytearray([19]) + struct.pack('>i', 0) + struct.pack('>H', 2) + struct.pack('>H', 65281)
    out += struct.pack('>H', cmd) + struct.pack('>H', 0) + struct.pack('>q', reqid)
    out += struct.pack('>i', 531) + struct.pack('>i', QMF_APP_ID) + struct.pack('>q', BIZ_ID)
    g = GUID.encode()[:32]
    out += g + b'\x00' * (32 - len(g))
    out += struct.pack('>b', QMF_PLATFORM) + struct.pack('>i', int(VER_CODE)) + b'\x00' * 6
    out += bytes([0]) + struct.pack('>H', 0) + struct.pack('>H', 0)
    out += struct.pack('>i', len(inner)) + comp + bytes([3])
    struct.pack_into('>i', out, 1, len(out))
    return bytes(out)


def _unwrap(data):
    if data[:1] != b'\x13' or len(data) < 90:
        return None
    flags = struct.unpack('>i', data[21:25])[0]
    payload = data[89:-1]
    if flags & 2:
        payload = gzip.decompress(payload)
    if payload[:1] != b'&' or payload[-1:] != b'(':
        return None
    rc = R(payload[16:-1]).struct()
    return rc.get(1) or b''


class DeadHostError(RuntimeError):
    pass


def jce_timeshift_url(pid, sid, start, end, stream='fhd'):
    w = W()
    w.string(pid, 0)
    w.string(sid, 1)
    w.long(start, 2)
    w.long(end, 3)
    w.string(stream, 4)
    body = w.out()
    cmd = 25312
    reqid = int(time.time() * 1000) & 2147483647
    packet = _wrap(cmd, body, reqid)
    req = urllib.request.Request('https://jacc.ysp.cctv.cn', data=packet, method='POST')
    req.add_header('Content-Type', 'application/octet-stream')
    with urllib.request.urlopen(req, timeout=15) as resp:
        raw = resp.read()
    resp_body = _unwrap(raw)
    if not resp_body:
        raise RuntimeError('bad response')
    m = R(resp_body).struct()
    err = m.get(0, 0)
    if err != 0:
        raise RuntimeError(m.get(1, 'errCode=%s' % err))
    url = m.get(2, '')
    if not url:
        raise RuntimeError('empty m3u8')
    if 'liverecord.video.cloud.cctv.com' in url:
        raise DeadHostError('dead cdn host')
    return url


# ---------------------------------------------------------------------------
# bkliveinfo 备用通道 (cKey 生成)
# ---------------------------------------------------------------------------
_CK_PLATFORM = 4330403
_CK_APPVER = 'V8.22.1035.3031'
_CK_TEA = bytes.fromhex('59b2f7cf725ef43c34fdd7c123411ed3')
_CK_GTEA = bytes.fromhex('110DBEC10C23E7D2E56A1CAD6914EF1B')
_CK_XOR = bytes([132, 46, 237, 8, 240, 102, 230, 234, 72, 180, 202, 169, 145, 237, 111, 243])
_CK_GXOR = bytes([179, 201, 83, 160, 105, 19, 173, 77])


def _u32(v):
    return v & 0xFFFFFFFF


def _tea_blk(blk, key):
    y, z = struct.unpack('>2I', blk)
    k = struct.unpack('>4I', key)
    s = 0
    for _ in range(16):
        s = _u32(s + 0x9E3779B9)
        y = _u32(y + _u32(_u32(_u32(z << 4) + k[0]) ^ _u32(z + s) ^ _u32((z >> 5) + k[1])))
        z = _u32(z + _u32(_u32(_u32(y << 4) + k[2]) ^ _u32(y + s) ^ _u32((y >> 5) + k[3])))
    return struct.pack('>2I', y, z)


def _cksum(buf):
    v = 0
    for b in buf:
        v = (131 * v + b) & 0x7FFFFFFF
    return v


def _tea_pkt(data, key):
    pad = (8 - (len(data) + 10) % 8) % 8
    plain = bytes([(os.urandom(1)[0] & 248) | pad]) + os.urandom(pad) + os.urandom(2) + data + bytes(7)
    out, pp, pc = b'', bytes(8), bytes(8)
    for off in range(0, len(plain), 8):
        mixed = bytes(a ^ b for a, b in zip(plain[off:off + 8], pc))
        enc = _tea_blk(mixed, key)
        cipher = bytes(a ^ b for a, b in zip(enc, pp))
        out += cipher
        pp, pc = mixed, cipher
    return out


def _lp(s):
    d = s.encode() if isinstance(s, str) else s
    return struct.pack('>H', len(d)) + d


def _ck_guard(ts, guid):
    def tail(v):
        t = str(v)
        return t[-5:] if len(t) >= 5 else ''

    body = struct.pack('>I', ts) + _lp(tail(guid)) + _lp(tail('null')) + _lp(tail('null')) + _lp('-1')
    plain = _lp(body)
    enc = _tea_pkt(plain, _CK_GTEA) + struct.pack('>I', _cksum(plain))
    enc = bytes(a ^ _CK_GXOR[i & 7] for i, a in enumerate(enc))
    return enc.hex().upper()


def _ckey(channel_id):
    ts = int(time.time())
    guid = os.urandom(16).hex()
    guard = _ck_guard(ts, guid)
    uid = os.urandom(4).hex().upper()
    body = (bytes.fromhex('0000004200000004000004d2') + struct.pack('>I', _CK_PLATFORM) + struct.pack('>I', 0)
            + struct.pack('>I', ts) + _lp('dcgh') + _lp('_zj1A5Gh6QYcxWjIUGos2w==') + _lp(_CK_APPVER)
            + _lp(str(channel_id)) + _lp(guid) + struct.pack('>I', 1) + struct.pack('>I', 1) + _lp(uid)
            + _lp('nil') + _lp('57eab0c4-2c58-44c6-8ae9-dd2757525dc5') + _lp('nil') + _lp('v0.1.000')
            + _lp('com.cctv.yangshipin.app.iphone') + _lp(str(_CK_PLATFORM)) + _lp('ex_json_bus')
            + _lp('ex_json_vs') + _lp(guard))
    pkt = bytearray(struct.pack('>H', len(body)) + body)
    pkt[18:22] = struct.pack('>I', _cksum(bytes(pkt)))
    pkt = bytes(pkt)
    enc = _tea_pkt(pkt, _CK_TEA) + struct.pack('>I', _cksum(pkt))
    enc = bytes(a ^ _CK_XOR[i & 15] for i, a in enumerate(enc))
    b64 = base64.b64encode(enc).decode().replace('+', '_').replace('/', '-').rstrip('=')
    return {'cKey': '--01' + b64, 'guid': guid, 'ts': ts,
            'flowId': '%s_%d' % (uuid.uuid4().hex.upper(), _CK_PLATFORM)}


_BK_H264 = base64.b64encode(b'H(30:1080,60:1080|30:1080,60:1080)').decode()


def bk_playurls(channel_id, live_pid, defn='fhd'):
    t = _ckey(channel_id)
    q = urllib.parse.urlencode({
        'atime': '120', 'livepid': live_pid, 'cnlid': channel_id, 'appVer': _CK_APPVER, 'app_version': '300090',
        'caplv': '1', 'cmd': '2', 'defn': defn, 'device': 'iPhone', 'encryptVer': '4.2', 'getpreviewinfo': '0',
        'hevclv': '0', 'lang': 'zh-Hans_CN', 'livequeue': '0', 'logintype': '1', 'nettype': '1',
        'newnettype': '1', 'newplatform': str(_CK_PLATFORM), 'platform': str(_CK_PLATFORM), 'sdtfrom': 'v3021',
        'spacode': '23', 'spaudio': '1', 'spdemuxer': '6', 'spdrm': '2', 'spdynamicrange': '1', 'spflv': '1',
        'spflvaudio': '1', 'sphdrfps': '60', 'sphttps': '1', 'spvcode': _BK_H264, 'spvideo': '4', 'stream': '1',
        'system': '1', 'sysver': 'ios18.2.1', 'uhd_flag': '0', 'cKey': t['cKey'], 'guid': t['guid'],
        'fntick': str(t['ts']), 'flowid': t['flowId'], 'playbacktime': '0'})
    req = urllib.request.Request('https://bkliveinfo.ysp.cctv.cn/?' + q,
                                 headers={'User-Agent': 'qqlive', 'Accept': 'application/json'})
    with urllib.request.urlopen(req, timeout=5) as r:
        p = json.loads(r.read().decode())
    if int(p.get('iretcode', -1)) != 0:
        raise RuntimeError('iretcode=%s %s' % (p.get('iretcode'), p.get('errinfo', '')))
    urls = []
    if p.get('playurl'):
        urls.append(p['playurl'])
    bu = p.get('backurl_list') or p.get('backurlList') or p.get('backurl')
    if isinstance(bu, list):
        for it in bu:
            urls.append(it if isinstance(it, str) else it.get('url') or it.get('playurl') or '')
    elif isinstance(bu, str):
        urls += [x for x in re.split('[;,]', bu) if x.strip()]
    urls = [u for u in dict.fromkeys(urls) if u and '.cctv.' in u]
    if not urls:
        raise RuntimeError('no playurl')
    urls.sort(key=lambda u: (0 if 'bklive-' in u else 1, u))
    return urls


def fetch_abs_playlist(url, depth=0):
    req = urllib.request.Request(url, headers={
        'User-Agent': 'qqlive', 'Referer': 'https://live.cctv.cn/',
        'Accept': 'application/vnd.apple.mpegurl,application/json,*/*'})
    with urllib.request.urlopen(req, timeout=10) as r:
        text = r.read().decode('utf-8', 'replace')
        final = r.geturl()
    if depth < 2:
        lines = text.splitlines()
        for i, ln in enumerate(lines):
            if ln.strip().startswith('#EXT-X-STREAM-INF'):
                for j in range(i + 1, len(lines)):
                    s = lines[j].strip()
                    if s and not s.startswith('#'):
                        return fetch_abs_playlist(urllib.parse.urljoin(final, s), depth + 1)
                break
    out = []
    for ln in text.splitlines():
        s = ln.strip()
        if s and not s.startswith('#'):
            out.append(urllib.parse.urljoin(final, s))
        else:
            out.append(ln)
    return '\n'.join(out)


# ---------------------------------------------------------------------------
# 频道表
# ---------------------------------------------------------------------------
DEFAULT_CHANNELS = [
    ('cctv1', 'CCTV-1 综合', '2024078201', '600001859', 'fhd'),
    ('cctv2', 'CCTV-2 财经', '2024075401', '600001800', 'fhd'),
    ('cctv3', 'CCTV-3 综艺', '2024068501', '600001801', 'fhd'),
    ('cctv4', 'CCTV-4 中文国际', '2029797101', '600001814', 'fhd'),
    ('cctv5', 'CCTV-5 体育', '2024078401', '600001818', 'fhd'),
    ('cctv5p', 'CCTV-5+ 体育赛事', '2024078001', '600001817', 'fhd'),
    ('cctv6', 'CCTV-6 电影', '2013693901', '600108442', 'fhd'),
    ('cctv7', 'CCTV-7 国防军事', '2024072001', '600004092', 'fhd'),
    ('cctv8', 'CCTV-8 电视剧', '2029793001', '600001803', 'fhd'),
    ('cctv9', 'CCTV-9 纪录', '2024078601', '600004078', 'fhd'),
    ('cctv10', 'CCTV-10 科教', '2024078701', '600001805', 'fhd'),
    ('cctv11', 'CCTV-11 戏曲', '2027248701', '600001806', 'fhd'),
    ('cctv12', 'CCTV-12 社会与法', '2027248801', '600001807', 'fhd'),
    ('cctv13', 'CCTV-13 新闻', '2029797201', '600001811', 'fhd'),
    ('cctv14', 'CCTV-14 少儿', '2027248901', '600001809', 'fhd'),
    ('cctv15', 'CCTV-15 音乐', '2027249001', '600001815', 'fhd'),
    ('cctv16', 'CCTV-16 奥林匹克', '2027249101', '600098637', 'fhd'),
    ('cctv164k', 'CCTV-16 4K', '2027249301', '600099502', 'fhd'),
    ('cctv17', 'CCTV-17 农业农村', '2027249401', '600001810', 'fhd'),
    ('cctv4k', 'CCTV-4K 超高清', '2029810301', '600002264', 'fhd'),
    ('cctv8k', 'CCTV-8K 超高清', '2026774101', '600156816', 'fhd'),
    ('cgtn', 'CGTN', '2024181701', '600014550', 'fhd'),
    ('cgtnfr', 'CGTN 法语', '2024181801', '600084704', 'fhd'),
    ('cgtnru', 'CGTN 俄语', '2024181901', '600084758', 'fhd'),
    ('cgtnar', 'CGTN 阿拉伯语', '2024182001', '600084782', 'fhd'),
    ('cgtnes', 'CGTN 西班牙语', '2024182101', '600084744', 'fhd'),
    ('cgtndoc', 'CGTN 纪录', '2024182301', '600084781', 'fhd'),
    ('cctvfyjc', 'CCTV 风云剧场', '2025637102', '600099658', 'shd'),
    ('cctvdyjc', 'CCTV 第一剧场', '2026874202', '600099655', 'shd'),
    ('cctvhjjc', 'CCTV 怀旧剧场', '2026874302', '600099620', 'shd'),
    ('bjws', '北京卫视', '2024052703', '600002309', 'fhd'),
    ('jsws', '江苏卫视', '2024171103', '600002521', 'fhd'),
    ('dfws', '东方卫视', '2024054503', '600002483', 'fhd'),
    ('zjws', '浙江卫视', '2024054703', '600002520', 'fhd'),
    ('hnws', '湖南卫视', '2024054803', '600002475', 'fhd'),
    ('hbws', '湖北卫视', '2024171203', '600002508', 'fhd'),
    ('gdws', '广东卫视', '2024060903', '600002485', 'fhd'),
    ('gxws', '广西卫视', '2024060703', '600002509', 'fhd'),
    ('hljws', '黑龙江卫视', '2029797003', '600002498', 'fhd'),
    ('hainanws', '海南卫视', '2024055603', '600002506', 'fhd'),
    ('cqws', '重庆卫视', '2024061103', '600002531', 'fhd'),
    ('szws', '深圳卫视', '2024061303', '600002481', 'fhd'),
    ('scws', '四川卫视', '2024061403', '600002516', 'fhd'),
    ('henanws', '河南卫视', '2029797303', '600002525', 'fhd'),
    ('dnws', '东南卫视', '2024061503', '600002484', 'fhd'),
    ('gzws', '贵州卫视', '2024061603', '600002490', 'fhd'),
    ('jxws', '江西卫视', '2024061703', '600002503', 'fhd'),
    ('lnws', '辽宁卫视', '2024171303', '600002505', 'fhd'),
    ('ahws', '安徽卫视', '2024171403', '600002532', 'fhd'),
    ('hebws', '河北卫视', '2024171503', '600002493', 'fhd'),
    ('sdws', '山东卫视', '2029787903', '600002513', 'fhd'),
    ('tjws', '天津卫视', '2019927003', '600152137', 'fhd'),
    ('jlws', '吉林卫视', '2025561503', '600190405', 'fhd'),
    ('saxws', '陕西卫视', '2029795103', '600190400', 'fhd'),
    ('nxws', '宁夏卫视', '2025608503', '600190737', 'fhd'),
    ('nmgws', '内蒙古卫视', '2025561203', '600190401', 'fhd'),
    ('ynws', '云南卫视', '2025561303', '600190402', 'fhd'),
    ('shanxiws', '山西卫视', '2025560803', '600190407', 'fhd'),
    ('gsws', '甘肃卫视', '2025561703', '600190408', 'fhd'),
    ('qhws', '青海卫视', '2025559103', '600190406', 'fhd'),
    ('xizangws', '西藏卫视', '2025558003', '600190403', 'fhd'),
    ('xjws', '新疆卫视', '2019927403', '600152138', 'fhd'),
    ('cetv1', 'CETV-1', '2022823801', '600171827', 'fhd'),
    ('guoxue', '国学频道', '2029360403', '600213139', 'fhd'),
]

ALIAS_MAP = {
    'anhuiws': 'ahws', 'beijingws': 'bjws', 'cctv16hd': 'cctv16', 'cctv5plus': 'cctv5p',
    'cctvdiyijuchang': 'cctvdyjc', 'cctvfengyunjuchang': 'cctvfyjc', 'cctvhuaijiujuchang': 'cctvhjjc',
    'cgtnalaboyu': 'cgtnar', 'cgtneyu': 'cgtnru', 'cgtnfayu': 'cgtnfr', 'cgtnwaiyujilu': 'cgtndoc',
    'cgtnxibanyayu': 'cgtnes', 'chongqingws': 'cqws', 'dongfangws': 'dfws', 'fujiandongnanws': 'dnws',
    'guangdongws': 'gdws', 'guangxiws': 'gxws', 'guizhouws': 'gzws', 'hebeiws': 'hebws',
    'heilongjiangws': 'hljws', 'hubeiws': 'hbws', 'hunanws': 'hnws', 'jiangsuws': 'jsws',
    'jiangxiws': 'jxws', 'jilinws': 'jlws', 'liaoningws': 'lnws', 'neimengguws': 'nmgws',
    'ningxiaws': 'nxws', 'qinghaiws': 'qhws', 'shandongws': 'sdws', 'shannxiws': 'saxws',
    'shenzhenws': 'szws', 'sichuanws': 'scws', 'tianjinws': 'tjws', 'xinjiangws': 'xjws',
    'yunnanws': 'ynws', 'zhejiangws': 'zjws',
}

TVG_IDS = {
    'cctv1': 'CCTV1', 'cctv2': 'CCTV2', 'cctv3': 'CCTV3', 'cctv4': 'CCTV4',
    'cctv5': 'CCTV5', 'cctv5p': 'CCTV5+', 'cctv6': 'CCTV6', 'cctv7': 'CCTV7',
    'cctv8': 'CCTV8', 'cctv9': 'CCTV9', 'cctv10': 'CCTV10', 'cctv11': 'CCTV11',
    'cctv12': 'CCTV12', 'cctv13': 'CCTV13', 'cctv14': 'CCTV14', 'cctv15': 'CCTV15',
    'cctv16': 'CCTV16', 'cctv164k': 'CCTV16', 'cctv17': 'CCTV17', 'cctv4k': 'CCTV4K',
    'cctv8k': 'CCTV-8K', 'cgtn': 'CGTN英语', 'cgtnfr': 'CGTN法语', 'cgtnru': 'CGTN俄语',
    'cgtnar': 'CGTN阿语', 'cgtnes': 'CGTN西语', 'cgtndoc': 'CGTN纪录',
    'cctvdyjc': 'CCTV第一剧场', 'cctvfyjc': 'CCTV风云剧场', 'cctvhjjc': 'CCTV怀旧剧场',
    'cetv1': 'CETV1', 'bjws': '北京卫视', 'jsws': '江苏卫视', 'dfws': '东方卫视',
    'zjws': '浙江卫视', 'hnws': '湖南卫视', 'hbws': '湖北卫视', 'gdws': '广东卫视',
    'gxws': '广西卫视', 'hljws': '黑龙江卫视', 'hainanws': '海南卫视', 'cqws': '重庆卫视',
    'szws': '深圳卫视', 'scws': '四川卫视', 'henanws': '河南卫视', 'dnws': '东南卫视',
    'gzws': '贵州卫视', 'jxws': '江西卫视', 'lnws': '辽宁卫视', 'ahws': '安徽卫视',
    'hebws': '河北卫视', 'sdws': '山东卫视', 'tjws': '天津卫视', 'jlws': '吉林卫视',
    'saxws': '陕西卫视', 'nxws': '宁夏卫视', 'nmgws': '内蒙古卫视', 'ynws': '云南卫视',
    'shanxiws': '山西卫视', 'qhws': '青海卫视', 'xizangws': '西藏卫视', 'xjws': '新疆卫视',
    'gsws': '甘肃卫视', 'guoxue': '国学',
}

LOGO_BASE = 'https://garysclub.sharewithyou.dpdns.org/logos/ysp-live-logos'
UA = 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36'
REFRESH_INTERVAL = 2
IDLE_TIMEOUT = 120
WINDOW = 1800
MAX_SEGS = 400
BK_URL_TTL = 300
BACKEND_CHANNELS = {
    'cctv1', 'cctv2', 'cctv3', 'cctv4', 'cctv5', 'cctv5p', 'cctv7', 'cctv8',
    'cctv9', 'cctv10', 'cctv11', 'cctv12', 'cctv13', 'cctv14', 'cctv15',
    'cctv16', 'cctv17', 'cctv4k', 'cctv8k', 'cctv164k', 'cgtn', 'cgtnfr',
    'cgtnru', 'cgtnar', 'cgtnes', 'cgtndoc',
}
active_backend_channels = set(BACKEND_CHANNELS)
TIMESHIFT_SUPPORTED = {
    'cctv1', 'cctv2', 'cctv3', 'cctv4', 'cctv5', 'cctv5p', 'cctv6', 'cctv7', 'cctv8', 'cctv9', 'cctv10', 'cctv13', 'cctv8k',
    'cgtn', 'cgtnfr', 'cgtnru', 'cgtnar', 'cgtnes', 'cgtndoc', 'cetv1', 'guoxue',
    'bjws', 'jsws', 'dfws', 'zjws', 'hnws', 'hbws', 'gdws', 'gxws',
    'hljws', 'hainanws', 'cqws', 'szws', 'scws', 'henanws', 'dnws',
    'gzws', 'jxws', 'lnws', 'ahws', 'hebws', 'sdws', 'tjws', 'jlws',
    'saxws', 'nxws', 'nmgws', 'ynws', 'shanxiws', 'qhws', 'xizangws', 'xjws', 'gsws',
}


def get_channel_group(slug: str) -> str:
    s = ALIAS_MAP.get(slug.lower(), slug.lower())
    return '央视' if s.startswith('cctv') or s.startswith('cgtn') else '卫视'


def parse_catchup_time_val(val_str: str | None) -> int | None:
    if not val_str:
        return None
    digits = ''.join(c for c in val_str.strip() if c.isdigit())
    if not digits:
        return None
    if len(digits) == 10:
        return int(digits)
    if len(digits) == 13:
        return int(int(digits) / 1000)
    cst = datetime.timezone(datetime.timedelta(hours=8))
    for width, fmt in ((14, '%Y%m%d%H%M%S'), (12, '%Y%m%d%H%M')):
        if len(digits) == width:
            try:
                return int(datetime.datetime.strptime(digits, fmt).replace(tzinfo=cst).timestamp())
            except Exception:
                pass
    return None


def parse_catchup_query(query_str: str) -> tuple[int, int] | None:
    if not query_str:
        return None
    qs = urllib.parse.parse_qs(query_str)
    now = int(time.time())
    start_ts = None
    end_ts = None
    if 'playseek' in qs:
        ps = qs['playseek'][0]
        if '-' in ps:
            a, b = ps.split('-', 1)
            start_ts = parse_catchup_time_val(a)
            end_ts = parse_catchup_time_val(b)
        else:
            start_ts = parse_catchup_time_val(ps)
    if not start_ts and 'start' in qs:
        start_ts = parse_catchup_time_val(qs['start'][0])
    if not end_ts and 'end' in qs:
        end_ts = parse_catchup_time_val(qs['end'][0])
    if not start_ts and 'utc' in qs:
        start_ts = parse_catchup_time_val(qs['utc'][0])
    if not end_ts and 'lutc' in qs:
        end_ts = parse_catchup_time_val(qs['lutc'][0])
    if not start_ts and 'starttime' in qs:
        start_ts = parse_catchup_time_val(qs['starttime'][0])
    if not end_ts and 'endtime' in qs:
        end_ts = parse_catchup_time_val(qs['endtime'][0])
    if start_ts is not None:
        if end_ts is None or end_ts <= start_ts:
            end_ts = max(start_ts + 60, min(start_ts + 7200, now))
        return start_ts, end_ts
    return None


# ---------------------------------------------------------------------------
# 并发控制 / 缓存
# ---------------------------------------------------------------------------
_inflight_refresh: dict = {}
_inflight_lock = threading.Lock()


def coalesce_refresh(slug: str, refresh_fn, timeout=None):
    with _inflight_lock:
        ev = _inflight_refresh.get(slug)
        wait = ev is not None
        if not wait:
            ev = _inflight_refresh[slug] = threading.Event()
    if wait:
        ev.wait(timeout=6.0 if timeout is None else timeout)
        return

    def _run():
        try:
            refresh_fn()
        finally:
            with _inflight_lock:
                _inflight_refresh.pop(slug, None)
            ev.set()

    t = threading.Thread(target=_run, daemon=True)
    t.start()
    if timeout is not None:
        ev.wait(timeout=timeout)
    else:
        t.join()


class ApiFlowLimiter:
    """全局 API 限速。优化: 在锁内只预约时间槽, 睡眠放到锁外 (原版持锁睡眠, 期间连取时间都要排队)。"""

    def __init__(self, min_interval_ms: int = 700, jitter_ms: int = 250):
        self.min_interval = min_interval_ms / 1000.0
        self.jitter = jitter_ms / 1000.0
        self.lock = threading.Lock()
        self.next_slot = 0.0

    def wait_slot(self):
        with self.lock:
            now = time.time()
            slot = max(now, self.next_slot)
            self.next_slot = slot + self.min_interval + random.uniform(0.0, self.jitter)
        delay = slot - now
        if delay > 0:
            time.sleep(delay)


global_flow_limiter = ApiFlowLimiter()


class TsSegmentCache:
    """TS 分片内存缓存 (LRU + TTL)。

    原版问题: 用 dict + deque 记顺序, 同一 key 重复写入或过期读取时不从 deque 删除,
    会产生重复/过期条目, 后续淘汰时可能把刚写入的新分片误淘汰; 且 --cache-mb 0 并不能真正关闭。
    """

    def __init__(self, max_mb: int = 100, max_age_sec: int = 180):
        self.max_bytes = max(0, int(max_mb)) * 1024 * 1024
        self.max_age = max_age_sec
        self.lock = threading.Lock()
        self.cache: OrderedDict = OrderedDict()   # key -> (data, headers, expire_at)
        self.curr_bytes = 0
        self.hits = 0
        self.misses = 0

    def _drop(self, key):
        item = self.cache.pop(key, None)
        if item is not None:
            self.curr_bytes -= len(item[0])

    def get(self, key: str):
        with self.lock:
            item = self.cache.get(key)
            if item is None:
                self.misses += 1
                return None
            data, headers, expire_at = item
            if time.time() > expire_at:
                self._drop(key)
                self.misses += 1
                return None
            self.cache.move_to_end(key)
            self.hits += 1
            return data, headers

    def set(self, key: str, data: bytes, headers: dict):
        with self.lock:
            if self.max_bytes <= 0 or len(data) > self.max_bytes:
                return
            self._drop(key)
            now = time.time()
            while self.cache:                      # 先清掉队首已过期的
                first_key, (_, _, exp) = next(iter(self.cache.items()))
                if exp >= now:
                    break
                self._drop(first_key)
            while self.cache and self.curr_bytes + len(data) > self.max_bytes:
                self._drop(next(iter(self.cache)))
            self.cache[key] = (data, headers, now + self.max_age)
            self.curr_bytes += len(data)

    def stats(self) -> dict:
        with self.lock:
            total = max(1, self.hits + self.misses)
            return {'count': len(self.cache), 'size_mb': round(self.curr_bytes / (1024 * 1024), 2),
                    'hits': self.hits, 'misses': self.misses, 'hit_rate': f'{round(self.hits / total * 100, 1)}%'}


global_ts_cache = TsSegmentCache(max_mb=200)


class ChannelDirectory:
    def __init__(self):
        self.lock = threading.Lock()
        self.channels_meta: dict = {}
        self.canonical_slugs: list = []
        self.load_defaults()

    def load_defaults(self):
        self.canonical_slugs.clear()
        for slug, name, sid, pid, defn in DEFAULT_CHANNELS:
            self.channels_meta[slug] = {
                'slug': slug, 'name': name, 'sid': sid, 'pid': pid, 'defn': defn,
                'logo': f'{LOGO_BASE}/{slug}.png', 'group': get_channel_group(slug),
                'tvg_id': TVG_IDS.get(slug, slug.upper())}
            self.canonical_slugs.append(slug)

    def get_meta(self, slug: str) -> dict | None:
        slug = ALIAS_MAP.get(slug.lower(), slug.lower())
        with self.lock:
            return self.channels_meta.get(slug)

    def unique_channels(self) -> list:
        with self.lock:
            return [self.channels_meta[s] for s in self.canonical_slugs if s in self.channels_meta]


global_channel_dir = ChannelDirectory()


# ---------------------------------------------------------------------------
# 1080p 备用通道: 频道状态机
# ---------------------------------------------------------------------------
class Channel:
    def __init__(self, slug, name, sid, pid, defn):
        self.slug, self.name, self.sid, self.pid, self.defn = slug, name, sid, pid, defn
        self.lock = threading.Lock()
        self.segments = {}
        self.order = deque()
        self.seq = 0
        self.last_access = 0.0
        self.thread = None
        self.last_error = ''
        self.last_ok = 0.0
        self.mode = 'jce'
        self.last_pdt = ''
        self.bk_urls = []
        self.bk_urls_time = 0.0
        self.bk_playlist = ''
        self._starting = False
        self.last_built_playlist = ''
        self.last_built_time = 0.0
        self.last_m3u8_source = ''

    def swap_source(self, new: str) -> str:
        with self.lock:
            prev, self.last_m3u8_source = self.last_m3u8_source, new
            return prev

    def invalidate_built(self):
        with self.lock:
            self.last_built_playlist = ''
            self.last_built_time = 0.0

    def release_buffers(self):
        """空闲收尾 (调用方需持有 self.lock)。"""
        self.segments.clear()
        self.order.clear()
        self.last_pdt = ''
        self.bk_playlist = ''
        self.last_built_playlist = ''
        self.last_built_time = 0.0


def seg_key(url, pdt):
    if pdt:
        return 'pdt:' + pdt
    p = urllib.parse.urlsplit(url)
    return p.scheme + '://' + p.netloc + p.path


def jce_fetch(ch):
    global_flow_limiter.wait_slot()
    now = int(time.time())
    m3u8_url = jce_timeshift_url(ch.pid, ch.sid, now - WINDOW, now, ch.defn)
    text = ''
    for attempt in range(3):
        try:
            req = urllib.request.Request(m3u8_url, headers={'User-Agent': UA})
            with urllib.request.urlopen(req, timeout=20) as r:
                text = r.read().decode('utf-8', 'replace')
            break
        except urllib.error.HTTPError as e:
            # 4xx 重试没有意义, 只对 5xx 重试 (原版对所有 URLError 含 HTTPError 一律重试)
            if attempt == 2 or e.code < 500:
                raise
            time.sleep(1)
        except (urllib.error.URLError, ssl.SSLError, OSError, http.client.HTTPException) as e:
            # 原版只捕获 URLError, 读响应阶段的 SSLError/ConnectionReset 等会直接穿透
            if attempt == 2:
                raise
            log(f'[{ch.slug}] jce 网络重试 {attempt + 1}/3: {e}', min_interval=5.0)
            time.sleep(1)
    segs, dur, pdt = [], 6.0, ''
    for line in text.splitlines():
        line = line.strip()
        if line.startswith('#EXTINF:'):
            try:
                dur = float(line[len('#EXTINF:'):].split(',')[0])
            except ValueError:
                dur = 6.0
        elif line.startswith('#EXT-X-PROGRAM-DATE-TIME:'):
            pdt = line[len('#EXT-X-PROGRAM-DATE-TIME:'):]
        elif line and not line.startswith('#'):
            segs.append((dur, pdt, urllib.parse.urljoin(m3u8_url, line)))
            pdt = ''
    if not segs:
        raise RuntimeError('empty playlist')
    return segs


def defn_label(defn):
    d = (defn or '').strip().lower()
    if d == 'fhd':
        return '1080p'
    if d == 'shd':
        return '720p'
    return defn or '1080p'


def jce_refresh(ch):
    segs = jce_fetch(ch)
    with ch.lock:
        added = 0
        is_init = not ch.order
        if is_init:
            init_segs = segs[-MAX_SEGS:] if len(segs) > MAX_SEGS else segs
            for dur, pdt, url in init_segs:
                key = seg_key(url, pdt)
                ch.seq += 1
                ch.segments[key] = [ch.seq, dur, pdt, url]
                ch.order.append(key)
                added += 1
                if pdt:
                    ch.last_pdt = pdt
        else:
            for dur, pdt, url in segs:
                if pdt and ch.last_pdt and pdt <= ch.last_pdt:
                    continue
                key = seg_key(url, pdt)
                if key in ch.segments:
                    ch.segments[key][3] = url
                    continue
                ch.seq += 1
                ch.segments[key] = [ch.seq, dur, pdt, url]
                ch.order.append(key)
                if pdt:
                    ch.last_pdt = pdt
                added += 1
        while len(ch.order) > MAX_SEGS:
            ch.segments.pop(ch.order.popleft(), None)
        ch.last_error = ''
    if is_init and added:
        log(f'[{ch.slug}] {defn_label(ch.defn)} 备用流缓冲就绪 ({len(ch.segments)} 片)')
    return True


def bk_refresh(ch):
    global_flow_limiter.wait_slot()
    now = time.time()
    if now - ch.bk_urls_time > BK_URL_TTL or not ch.bk_urls:
        ch.bk_urls = bk_playurls(ch.sid, ch.pid, ch.defn)
        ch.bk_urls_time = now
        log(f'[{ch.slug}] bkliveinfo 备用通道就绪 ({len(ch.bk_urls)} 地址)', min_interval=60.0)
    last_err = ''
    for attempt in range(2):
        for u in ch.bk_urls:
            try:
                pl = fetch_abs_playlist(u)
                if '#EXTM3U' not in pl:
                    continue
                with ch.lock:
                    ch.bk_playlist = pl
                    ch.last_error = ''
                return True
            except urllib.error.HTTPError as e:
                last_err = 'HTTPError: HTTP %s' % e.code
            except Exception as e:
                last_err = '%s: %s' % (type(e).__name__, e)
        if attempt == 0:
            try:
                ch.bk_urls = bk_playurls(ch.sid, ch.pid, ch.defn)
                ch.bk_urls_time = time.time()
                log(f'[{ch.slug}] {defn_label(ch.defn)} 地址已过期，已重新拉取', min_interval=10.0)
            except Exception:
                pass
    ch.bk_urls = []
    ch.bk_urls_time = 0
    raise RuntimeError(last_err[:120] or 'bk playlist failed')


def refresh_once(ch):
    try:
        if ch.mode == 'bk':
            ok = bk_refresh(ch)
        else:
            try:
                ok = jce_refresh(ch)
            except DeadHostError:
                ch.mode = 'bk'
                log(f'[{ch.slug}] JCE 域名受限，自动切换 bkliveinfo 备用通道', min_interval=10.0)
                ok = bk_refresh(ch)
        if ok:
            ch.last_ok = time.time()
        return ok
    except Exception as e:
        ch.last_error = ('%s: %s' % (type(e).__name__, e))[:120]
        log(f'[{ch.slug}] {defn_label(ch.defn)} 刷新异常: {ch.last_error}', min_interval=15.0)
        return False


def refresh_loop(ch):
    """后台拉取线程。

    修复: 原版 `while True` 永不退出, IDLE_TIMEOUT 常量从未使用, 访问过的每个频道都会
    永远每 2 秒轮询上游; 全局限速又把所有频道串行化, 访问频道越多越慢。
    现在空闲超过 IDLE_TIMEOUT 秒会自动停止并释放缓冲, 下次访问由 ensure_channel 重新拉起。
    """
    log(f'[{ch.slug}] {defn_label(ch.defn)} 后台拉取启动 [{ch.mode}]', min_interval=10.0)
    fails = 0
    while True:
        if time.time() - ch.last_access > IDLE_TIMEOUT:
            with ch.lock:
                if time.time() - ch.last_access > IDLE_TIMEOUT:   # 持锁复查, 避免与 ensure_channel 竞争
                    ch.release_buffers()
                    ch.thread = None
                    break
        try:
            ok = refresh_once(ch)
            if ok:
                build_playlist(ch, holdback=True)
        except Exception as e:
            ok = False
            log(f'[{ch.slug}] 后台线程异常: {type(e).__name__}: {e}', min_interval=15.0)
        fails = 0 if ok else fails + 1
        time.sleep(REFRESH_INTERVAL if fails < 3 else 30)
    log(f'[{ch.slug}] 空闲超时，已停止后台拉取', min_interval=10.0)


def ensure_channel(ch):
    ch.last_access = time.time()
    with ch.lock:
        if ch._starting:
            return
        thread_dead = ch.thread is None or not ch.thread.is_alive()
        need_fetch = not ch.segments and not ch.bk_playlist
        if need_fetch:
            ch.segments.clear()
            ch.order.clear()
            ch.last_pdt = ''
            ch.bk_playlist = ''
        if not (need_fetch or thread_dead):
            return
        ch._starting = True
    try:
        if need_fetch:
            coalesce_refresh(ch.slug, lambda: refresh_once(ch), timeout=5.0)
        if thread_dead:
            t = threading.Thread(target=refresh_loop, args=(ch,), daemon=True)
            with ch.lock:
                ch.thread = t
            t.start()
    finally:
        with ch.lock:
            ch._starting = False


def build_playlist(ch, holdback: bool = True):
    with ch.lock:
        if ch.mode == 'bk':
            res = ch.bk_playlist or None
            if res:
                ch.last_built_playlist = res
                ch.last_built_time = time.time()
            return res
        keys = list(ch.order)[-MAX_SEGS:]
        segs = [ch.segments[k] for k in keys if k in ch.segments]
    if not segs:
        return None
    display_segs = segs[:-20] if holdback and len(segs) >= 24 else segs
    target = max(6, max(int(s[1] + 0.5) for s in display_segs))
    out = ['#EXTM3U', '#EXT-X-VERSION:3', '#EXT-X-TARGETDURATION:%d' % target,
           '#EXT-X-MEDIA-SEQUENCE:%d' % display_segs[0][0]]
    for _, dur, pdt, url in display_segs:
        if pdt:
            out.append('#EXT-X-PROGRAM-DATE-TIME:' + pdt)
        out.append('#EXTINF:%.3f,' % dur)
        out.append(url)
    res = '\n'.join(out) + '\n'
    with ch.lock:
        ch.last_built_playlist = res
        ch.last_built_time = time.time()
    return res


def trigger_background_refresh(ch):
    with _inflight_lock:
        if ch.slug in _inflight_refresh:
            return

    def _do():
        if refresh_once(ch):
            build_playlist(ch, holdback=True)

    threading.Thread(target=coalesce_refresh, args=(ch.slug, _do), daemon=True).start()


def insert_discontinuity(playlist: str) -> str:
    """在第一个分片之前插入 #EXT-X-DISCONTINUITY。

    原版把标签插在 #EXTM3U 之后、#EXT-X-VERSION 之前, 位置不合法 (必须出现在分片条目之前)。
    """
    lines = playlist.split('\n')
    for i, ln in enumerate(lines):
        if ln.startswith('#EXTINF') or ln.startswith('#EXT-X-PROGRAM-DATE-TIME'):
            lines.insert(i, '#EXT-X-DISCONTINUITY')
            return '\n'.join(lines)
    return playlist


CHANNEL_MAP: dict = {c[0]: Channel(*c) for c in DEFAULT_CHANNELS}
FORCE_BK = {'cctv11', 'cctv12', 'cctv14', 'cctv15', 'cctv16', 'cctv17', 'cctvfyjc', 'cctvdyjc', 'cctvhjjc'}
for _s in FORCE_BK:
    if _s in CHANNEL_MAP:
        CHANNEL_MAP[_s].mode = 'bk'

server_port: int = 8767
server_start_time = time.time()
resolver: Resolver | None = None
_resolver_ready: bool = False
_resolver_lock = threading.Lock()


def resolver_ready() -> bool:
    with _resolver_lock:
        return _resolver_ready


def set_resolver_ready(ready: bool) -> None:
    global _resolver_ready
    with _resolver_lock:
        _resolver_ready = ready


def get_channel_instance(slug: str) -> Channel | None:
    slug = normalize_channel(slug)
    canonical = ALIAS_MAP.get(slug, slug)
    if canonical in CHANNEL_MAP:
        return CHANNEL_MAP[canonical]
    meta = global_channel_dir.get_meta(canonical)
    if meta:
        ch = Channel(meta['slug'], meta['name'], meta['sid'], meta['pid'], meta['defn'])
        if canonical in FORCE_BK:
            ch.mode = 'bk'
        CHANNEL_MAP[canonical] = ch
        return ch
    return None


# ---------------------------------------------------------------------------
# HTTP 服务
# ---------------------------------------------------------------------------
engine_port = 8787
TS_PASS_HEADERS = ('content-type', 'content-range', 'accept-ranges', 'content-length')
TS_CACHE_MAX_ITEM = 35 * 1024 * 1024
HOST_RE = re.compile(r'^[A-Za-z0-9._\-:\[\]]+$')
M3U8_CT = 'application/vnd.apple.mpegurl'


def fetch_upstream_engine_playlist(canonical: str, host: str, scheme: str = 'http') -> str | None:
    for u in (f'http://127.0.0.1:{engine_port}/live/{canonical}.m3u8',
              f'http://127.0.0.1:{engine_port}/{canonical}.m3u8'):
        try:
            req = urllib.request.Request(u, headers={'User-Agent': UA})
            with urllib.request.urlopen(req, timeout=10.0) as resp:
                if resp.status != 200:
                    continue
                text = resp.read().decode('utf-8', errors='ignore')
            if '#EXTM3U' not in text:
                continue
            base_prefix = f'{scheme}://{host}/engine_proxy?url='
            out_lines = []
            for line in text.splitlines():
                s = line.strip()
                if not s:
                    continue
                if s.startswith('#'):
                    out_lines.append(s)
                else:
                    full = s if s.startswith(('http://', 'https://')) else urllib.parse.urljoin(u, s)
                    out_lines.append(base_prefix + urllib.parse.quote(full, safe='') + '&sig=' + sign_value(full))
            return '\n'.join(out_lines) + '\n'
        except Exception:
            pass
    return None


class Server(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 128      # 默认只有 5, 多设备同时拉流时容易 SYN 队列溢出


class Handler(BaseHTTPRequestHandler):
    server_version = f'ysp-live/{__version__}'
    timeout = 60                  # 慢客户端 / 僵死连接不再无限占用线程

    def log_message(self, fmt, *args):
        pass

    # ----- 基础 -----------------------------------------------------------
    def _send(self, code, body, ctype='text/plain; charset=utf-8', head_only=False, extra_headers=None):
        data = body.encode('utf-8') if isinstance(body, str) else body
        try:
            self.send_response(code)
            self.send_header('Content-Type', ctype)
            self.send_header('Content-Length', str(len(data)))
            self.send_header('Access-Control-Allow-Origin', '*')
            self.send_header('Cache-Control', 'no-cache, no-store, max-age=0')
            if extra_headers:
                for k, v in extra_headers.items():
                    self.send_header(k, v)
            self.end_headers()
            if not head_only:
                self.wfile.write(data)
        except OSError:
            pass

    def _host_and_scheme(self):
        host = (self.headers.get('Host') or '').strip()
        if not host or not HOST_RE.match(host):          # 防止 Host 头注入进播放列表
            host = f'localhost:{server_port}'
        proto = (self.headers.get('X-Forwarded-Proto') or 'http').split(',')[0].strip().lower()
        return host, proto if proto in ('http', 'https') else 'http'

    def do_HEAD(self):
        self.do_GET(head_only=True)

    def do_GET(self, head_only=False):
        try:
            self._route(head_only)
        except OSError:
            pass
        except Exception as e:
            log(f'[HTTP] {urllib.parse.urlsplit(self.path).path[:80]} 处理异常: {type(e).__name__}: {e}', min_interval=5.0)
            self._send(500, 'internal error\n', head_only=head_only)

    def _route(self, head_only):
        parts = urllib.parse.urlsplit(self.path)
        path = parts.path
        if path in ('/', '/index.html'):
            return self._serve_index(head_only)
        if path == '/favicon.ico':
            fav = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100"><text y=".9em" font-size="90">📺</text></svg>'
            return self._send(200, fav, 'image/svg+xml', head_only=head_only)
        if path == '/health':
            return self._serve_health(head_only)
        if path == '/all.m3u':
            return self._serve_all_m3u(parts, head_only)
        if path == '/diag':
            return self._serve_diag(head_only)
        if path in ('/proxy.ts', '/proxy'):
            return self._serve_ts(head_only)
        if path == '/engine_proxy':
            return self._serve_engine_proxy(parts, head_only)
        m = re.match(r'^/([\w-]+)\.m3u8$', path)
        if m:
            return self._serve_channel(m, parts, head_only)
        self._send(404, 'not found\n', head_only=head_only)

    # ----- 信息页 ---------------------------------------------------------
    def _serve_index(self, head_only):
        host, _ = self._host_and_scheme()
        text = (
            f'====================================================\n'
            f'ysp-live IPTV 直播网关运行中 (端口: {server_port})\n'
            f'📢 官方发布社区: {AUTHOR_COMMUNITY}\n'
            f'📢 官方发布频道: {AUTHOR_CHANNEL}\n'
            f'⚠️ 严正声明: 其他任何渠道均非作者发布！\n'
            f'====================================================\n\n'
            f'全频道订阅: http://{host}/all.m3u\n'
            f'系统健康度: http://{host}/health\n'
            f'实时诊断日志: http://{host}/diag\n')
        self._send(200, text, head_only=head_only)

    def _serve_health(self, head_only):
        now = time.time()
        sess = None
        active_slots = 0
        if resolver:
            with resolver.state_lock:
                sess = resolver.state.app_session
                sessions = list(resolver.state.sessions.values())
            active_slots = sum(1 for s in sessions if s and resolver.app_session_fresh(s))
        # 不再对外输出 cloud_guid (设备注册标识)
        data = {
            'ok': True, 'version': __version__,
            'author_community': AUTHOR_COMMUNITY, 'author_channel': AUTHOR_CHANNEL,
            'notice': '其他渠道均非作者发布！', 'uptime_sec': int(now - server_start_time),
            'engine': {
                'ready': resolver_ready(), 'active_device_slots': active_slots,
                'session_valid': bool(sess and resolver and resolver.app_session_fresh(sess)),
                'heartbeat_count': sess.heartbeat_count if sess else 0,
            },
            'channels': len(global_channel_dir.unique_channels()),
            'ts_cache': global_ts_cache.stats(),
            'routes': ['/', '/all.m3u', '/diag', '/health', '/<channel>.m3u8', '/proxy.ts'],
        }
        self._send(200, json.dumps(data, ensure_ascii=False, indent=2), 'application/json; charset=utf-8', head_only=head_only)

    def _serve_all_m3u(self, parts, head_only):
        host, proto = self._host_and_scheme()
        qs = urllib.parse.parse_qs(parts.query)
        target_group = qs.get('group', [None])[0]
        only_4k = qs.get('k4', ['0'])[0].lower() in ('1', 'true', 'yes')
        lines = [
            '#EXTM3U url-tvg="https://epg.zsdc.eu.org/t.xml.gz,https://epg.pw/xmltv/epg_CN.xml.gz" x-tvg-url="https://epg.zsdc.eu.org/t.xml.gz"',
            '#EXT-X-APTV-PREVIEW: FALSE', '#EXT-X-APTV-LATENCY: FALSE', '#EXT-X-APTV-LOGO: FALSE',
        ]
        for meta in global_channel_dir.unique_channels():
            slug, name, grp = meta['slug'], meta['name'], meta['group']
            if target_group and target_group not in grp:
                continue
            if only_4k and slug not in TRUE_4K_CHANNELS:
                continue
            attrs = f' tvg-id="{meta["tvg_id"]}" tvg-name="{name}" tvg-logo="{meta["logo"]}" group-title="{grp}"'
            if slug in TIMESHIFT_SUPPORTED:
                attrs += ' catchup="append" catchup-days="7" catchup-source="?playseek=${(b)yyyyMMddHHmmss}-${(e)yyyyMMddHHmmss}"'
            lines.append(f'#EXTINF:-1{attrs},{name}')
            lines.append(f'{proto}://{host}/{slug}.m3u8')
        self._send(200, '\n'.join(lines) + '\n', M3U8_CT, head_only=head_only)

    def _serve_diag(self, head_only):
        now = time.time()
        info = [
            '====================================================',
            f'ysp-live v{__version__} 诊断报告 (运行时间: {int(now - server_start_time)}s)',
            f'官方社区: {AUTHOR_COMMUNITY}',
            f'首发频道: {AUTHOR_CHANNEL}',
            '====================================================',
        ]
        s0 = None
        if resolver:
            with resolver.state_lock:
                s0 = resolver.state.sessions.get(0)
        links_limit_cfg = getattr(resolver.args, 'links_per_device', 6) if resolver else 6
        engine_status = '就绪' if resolver_ready() else '未就绪(1080p自动回退)'
        valid = '有效' if s0 and resolver and resolver.app_session_fresh(s0) else '未就绪'
        info.append(f'单设备并发池状态: {engine_status}')
        info.append(f'高码率设备状态 (26 路共用): {valid}, 占用={len(s0.linked_channels) if s0 else 0}/{links_limit_cfg}, '
                    f'心跳={s0.heartbeat_count if s0 else 0}, 已注册={"是" if s0 and s0.cloud_guid else "否"}')
        if s0 and s0.last_heartbeat_error:
            info.append(f'Slot 0 心跳日志: {s0.last_heartbeat_error}')
        c = global_ts_cache.stats()
        info.append(f"分片内存缓存: 条目={c['count']}, 占用={c['size_mb']}MB, 命中率={c['hit_rate']} (命中:{c['hits']}/未中:{c['misses']})")
        info.append('--- 频道状态列表 ---')
        for meta in global_channel_dir.unique_channels():
            slug = meta['slug']
            ch = CHANNEL_MAP.get(slug)
            age = '%ds前' % int(now - ch.last_ok) if ch and ch.last_ok else '从未拉取'
            mode_str = '4K/高码率' if slug in active_backend_channels and resolver_ready() else (ch.mode if ch else 'idle')
            cooldown_str = ''
            if resolver and resolver.is_channel_in_cooldown(slug):
                fail_info = resolver.get_channel_failure_info(slug)
                if fail_info:
                    rem_sec = max(0, int(cooldown_for(fail_info[2]) - (now - fail_info[0])))
                    cooldown_str = f' [高码冷却剩{rem_sec}s]'
            err_msg = ch.last_error if ch else '无'
            info.append(f"{slug} ({meta['name']}) 模式={mode_str}{cooldown_str} 上次刷新={age} 错误={err_msg or '无'}")
        if global_log_ring:
            info.append('--- 最近运行事件 (最新 30 条) ---')
            info.extend(re.sub(r'\033\[[0-9;]*m', '', line) for line in list(global_log_ring)[-30:])
        self._send(200, '\n'.join(info) + '\n', head_only=head_only)

    # ----- 分片代理 -------------------------------------------------------
    def _send_cached_ts(self, item, head_only):
        data, headers = item
        try:
            self.send_response(200)
            for k, v in headers.items():
                self.send_header(k, v)
            if not any(k.lower() == 'content-length' for k in headers):
                self.send_header('Content-Length', str(len(data)))
            self.send_header('X-Cache', 'HIT-RAM')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.send_header('Cache-Control', 'public, max-age=300')
            self.end_headers()
            if not head_only:
                self.wfile.write(data)
        except OSError:
            pass

    def _serve_ts(self, head_only):
        token = proxy_ts_token(self.path)
        if not token:
            return self._send(400, 'missing proxy ts token\n', head_only=head_only)
        try:
            real_url = decode_proxy_ts_url(token)
        except YsptpError as err:
            return self._send(400, f'{err}\n', head_only=head_only)
        range_header = self.headers.get('Range')
        if not range_header:                      # 带 Range 的请求绕过缓存, 避免对 Range 返回 200 全量
            cached = global_ts_cache.get(real_url)
            if cached is not None:
                return self._send_cached_ts(cached, head_only)
        try:
            playback_headers = resolver.playback_headers_for_ts_url(real_url) if resolver else {}
        except YsptpError as err:
            return self._send(500, f'{err}\n', head_only=head_only)
        extra = {'Range': header_value_clean(range_header)} if range_header else None
        headers = _playback_request_headers(playback_headers, extra)
        try:
            conn, resp = open_upstream(real_url, headers, 'HEAD' if head_only else 'GET', timeout=30)
        except YsptpError as err:
            return self._send(502, f'Upstream CDN error: {err}\n', head_only=head_only)
        try:
            passthrough = {k: v for k, v in resp.getheaders() if k.lower() in TS_PASS_HEADERS}
            try:
                self.send_response(resp.status)
                for k, v in passthrough.items():
                    self.send_header(k, v)
                self.send_header('X-Cache', 'MISS-UPSTREAM')
                self.send_header('Access-Control-Allow-Origin', '*')
                self.send_header('Cache-Control', 'public, max-age=300')
                self.end_headers()
                if not head_only:
                    self._stream_and_cache(real_url, resp, passthrough)
            except (OSError, http.client.HTTPException):
                pass                              # 客户端断开 / 传输中途上游异常: 响应头已发出, 只能静默结束
        finally:
            conn.close()

    def _stream_and_cache(self, real_url, resp, passthrough):
        body = bytearray()
        oversize = False
        expected = None
        cl = next((v for k, v in passthrough.items() if k.lower() == 'content-length'), None)
        if cl:
            try:
                expected = int(cl)
                oversize = expected > TS_CACHE_MAX_ITEM
            except ValueError:
                pass
        cacheable = resp.status == 200
        while True:
            chunk = resp.read(262144)
            if not chunk:
                break
            self.wfile.write(chunk)
            if cacheable and not oversize:
                if len(body) + len(chunk) <= TS_CACHE_MAX_ITEM:
                    body.extend(chunk)
                else:
                    oversize = True
                    body.clear()
        if cacheable and not oversize and body and (expected is None or len(body) == expected):
            global_ts_cache.set(real_url, bytes(body), passthrough)

    def _serve_engine_proxy(self, parts, head_only):
        qs = urllib.parse.parse_qs(parts.query)
        target = qs.get('url', [''])[0]
        sig = qs.get('sig', [''])[0]
        if not target:
            return self._send(400, 'missing url\n', head_only=head_only)
        # 只代理本进程签发过的地址 (原版会请求任意 URL → SSRF / 开放代理)
        if not verify_signature(target, sig) or not target.startswith(('http://', 'https://')):
            return self._send(403, 'forbidden\n', head_only=head_only)
        try:
            req = urllib.request.Request(target, headers={'User-Agent': UA, 'Accept': '*/*'})
            with urllib.request.urlopen(req, timeout=10.0) as resp:
                data = resp.read()
                self._send(resp.status, data, resp.headers.get('Content-Type', 'video/mp2t'), head_only=head_only)
        except Exception as e:
            self._send(502, f'engine proxy error: {e}\n', head_only=head_only)

    # ----- 频道播放列表 ---------------------------------------------------
    def _send_playlist(self, ch, pl, source, head_only, extra_headers=None):
        prev = ch.swap_source(source)
        if prev and prev != source:
            pl = insert_discontinuity(pl)
        self._send(200, pl, M3U8_CT, head_only=head_only, extra_headers=extra_headers)

    def _serve_channel(self, m, parts, head_only):
        canonical = normalize_channel(m.group(1))
        canonical = ALIAS_MAP.get(canonical, canonical)
        ch = get_channel_instance(canonical)
        if not ch:
            return self._send(404, '未知频道\n', head_only=head_only)
        host, scheme = self._host_and_scheme()

        catchup_times = parse_catchup_query(parts.query)
        if catchup_times and canonical in TIMESHIFT_SUPPORTED:
            start_ts, end_ts = catchup_times
            try:
                pl = fetch_abs_playlist(jce_timeshift_url(ch.pid, ch.sid, start_ts, end_ts, ch.defn))
                return self._send(200, pl, M3U8_CT, head_only=head_only)
            except Exception as e:
                log(f'[{canonical}] 时移获取失败: {e}，回退直播', min_interval=10.0)

        # 1) 高码率 (设备协议)
        if canonical in active_backend_channels and resolver_ready() and resolver is not None \
                and not resolver.is_channel_in_cooldown(canonical):
            try:
                pl = resolver.fetch_channel_playlist(canonical, host, scheme)
                if pl and '#EXTM3U' in pl:
                    ch.invalidate_built()
                    return self._send_playlist(ch, pl, 'device', head_only)
            except Exception as e:
                fail_cnt = resolver.note_playlist_failure(canonical, e)
                log(f'[{canonical}] 高码率播放暂时受限 ({str(e).strip()})，平滑回退 1080p '
                    f'(冷却 {int(cooldown_for(fail_cnt))}s)', min_interval=5.0)

        # 2) 1080p 备用通道 (SWR 缓存)
        now_ts = time.time()
        ch.last_access = now_ts
        with ch.lock:
            cached_pl = ch.last_built_playlist
            cached_age = now_ts - ch.last_built_time
        if cached_pl and cached_age < 15.0 and '#EXTM3U' in cached_pl:
            self._send_playlist(ch, cached_pl, 'bk', head_only, {'X-SWR': 'HIT'})
            if cached_age > 6.0:
                trigger_background_refresh(ch)
            return
        ensure_channel(ch)
        pl = build_playlist(ch, holdback=True)
        if pl and '#EXTM3U' in pl:
            return self._send_playlist(ch, pl, 'bk', head_only)

        # 3) 伴生 Web WASM 引擎兜底
        upstream_pl = fetch_upstream_engine_playlist(canonical, host, scheme)
        if upstream_pl and '#EXTM3U' in upstream_pl:
            return self._send(200, upstream_pl, M3U8_CT, head_only=head_only)
        self._send(503, '频道 %s 暂无数据 (%s), 请稍后重试\n' % (ch.name, ch.last_error or '拉取中'), head_only=head_only)


# ---------------------------------------------------------------------------
# 启动
# ---------------------------------------------------------------------------
def init_resolver():
    if resolver is None:
        return
    log('[系统] 正在初始化设备协议并发池…')
    retry_count = 0
    while True:
        try:
            resolver.ensure_slot_session(0)
            set_resolver_ready(True)
            log('[系统] 设备身份就绪，高码率并发池已激活 (全部 26 路按需解析)')
            break
        except Exception as e:
            retry_count += 1
            log(f'[系统] 设备协议初始化第 {retry_count} 次重试中: {e}，4K/高码率频道暂走 1080p 回退', min_interval=10.0)
            set_resolver_ready(False)
            if 'HTTP 400' in str(e):
                resolver.rotate_device_on_400('init:' + str(e)[:60])
            time.sleep(min(15.0 * (1.5 ** min(retry_count - 1, 4)), 60.0))


companion_proc = None


def is_port_listening(port: int, host: str = '127.0.0.1') -> bool:
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.settimeout(0.5)
            return s.connect_ex((host, port)) == 0
    except Exception:
        return False


def start_companion_engine(script_dir: str, port: int = 8787):
    global companion_proc
    if is_port_listening(port):
        log(f'[引擎] Web WASM 引擎已就绪: 端口 {port} 已处于运行状态')
        return
    candidates = [os.path.join(script_dir, 'ysp-engine.js'), os.path.join(os.getcwd(), 'ysp-engine.js'), '/app/ysp-engine.js']
    engine_file = next((p for p in candidates if os.path.isfile(p)), None)
    if not engine_file:
        log('[引擎] 未找到 ysp-engine.js，Web WASM 伴生引擎未启用')
        return
    node_bin = shutil.which('node')
    if not node_bin:
        log('[引擎] 未检测到 node 可执行程序，Web WASM 伴生引擎未启用 (走设备协议/1080p 回退)')
        return
    try:
        companion_proc = subprocess.Popen([node_bin, engine_file, str(port)],
                                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(30):
            if is_port_listening(port):
                log(f'[引擎] Web WASM 伴生引擎 (Node.js) 自动启动成功: 端口 {port}')
                return
            time.sleep(0.1)
        if companion_proc.poll() is not None:
            log('[引擎] 警告: Web WASM 伴生引擎启动异常退出')
            companion_proc = None
        else:
            log(f'[引擎] Web WASM 伴生引擎已在后台启动 (端口 {port})')
    except Exception as e:
        log(f'[引擎] Web WASM 伴生引擎启动失败: {e}')
        companion_proc = None


def stop_companion_engine():
    global companion_proc
    if companion_proc is None:
        return
    p, companion_proc = companion_proc, None
    try:
        if p.poll() is None:
            p.terminate()
            try:
                p.wait(timeout=2.0)
            except Exception:
                p.kill()
        log('[引擎] Web WASM 伴生引擎 (Node.js) 已停止')
    except Exception:
        pass


atexit.register(stop_companion_engine)


def _handle_sigterm(signum, frame):
    stop_companion_engine()
    sys.exit(0)


try:
    signal.signal(signal.SIGTERM, _handle_sigterm)
except Exception:
    pass


def main():
    global resolver, server_port, engine_port, global_ts_cache, active_backend_channels
    if os.name == 'nt':
        os.system('')   # 让 Windows 控制台支持 ANSI 颜色
    ap = argparse.ArgumentParser(description=f'央视频全频道直播代理（ysp-live v{__version__}）')
    ap.add_argument('port', nargs='?', type=int, default=8767, help='监听端口 (默认 8767)')
    ap.add_argument('--bind', default='0.0.0.0', help='监听地址 (默认 0.0.0.0)')
    ap.add_argument('--data-dir', default=os.environ.get('YSP_DATA_DIR', ''), help='数据持久化目录 (默认由 YSP_DATA_DIR 环境变量或脚本所在目录决定)')
    ap.add_argument('--cache-mb', type=int, default=200, help='TS 分片内存缓存大小 (MB, 默认 200, 0 = 关闭)')
    ap.add_argument('--no-4k', action='store_true', help='不启动设备协议 (仅走 1080p JCE/bkliveinfo)')
    ap.add_argument('--only-4k', action='store_true', help='仅 4K/8K 频道走设备协议 (默认全部 26 个高码率频道走设备协议)')
    ap.add_argument('--links-per-device', type=int, default=int(os.environ.get('YSP_LINKS_PER_DEVICE', '6')), help='单设备高码率链接配额上限 (默认 6, 设为 0 关闭主动轮换)')
    ap.add_argument('--zap-debounce', type=float, default=float(os.environ.get('YSP_ZAP_DEBOUNCE', '10.0')), help='换台防抖秒数: 切台后先出 1080p, 停留超过该秒数才后台请求高码率 (默认 10.0, 设为 0 关闭)')
    ap.add_argument('--engine-port', type=int, default=8787, help='Web WASM 引擎端口 (默认 8787)')
    ap.add_argument('--timeout', type=float, default=10.0, help='设备协议 HTTP 超时秒数 (默认 10, 注册失败时更快回退 1080p)')
    ap.add_argument('--no-engine', action='store_true', help='不启动 Web WASM 伴生引擎')
    args = ap.parse_args()

    server_port = args.port
    engine_port = args.engine_port
    global_ts_cache = TsSegmentCache(max_mb=args.cache_mb)

    here = os.path.dirname(os.path.abspath(__file__))
    if not args.no_engine:
        start_companion_engine(here, engine_port)

    data_dir = args.data_dir or os.environ.get('YSP_DATA_DIR', here)
    if data_dir and not os.path.exists(data_dir):
        try:
            os.makedirs(data_dir, exist_ok=True)
        except OSError:
            data_dir = here
    test_file = os.path.join(data_dir, f'.perm_test_{os.getpid()}')
    try:
        with open(test_file, 'w') as f:
            f.write('ok')
        os.remove(test_file)
        log(f'[系统] 持久化存储目录: {data_dir} (读写权限正常)')
    except OSError as e:
        log(f'[系统] 警告: 持久化目录 {data_dir} 写入受限 ({e})，状态将保持内存模式')
    init_proxy_secret(data_dir)

    only_4k_mode = args.only_4k or os.environ.get('YSP_ONLY_4K_DEVICE', '').lower() in ('1', 'true', 'yes')
    links_limit = max(0, int(args.links_per_device))
    if only_4k_mode:
        active_backend_channels = set(TRUE_4K_CHANNELS)
        log('[系统] 高码率模式: 仅 4K/8K 频道走设备协议 (其余走 1080p JCE/bkliveinfo)')
    else:
        active_backend_channels = set(BACKEND_CHANNELS)
        log(f'[系统] 高码率模式: 全部 26 个高码率频道走单设备并发池 (1 台设备, 高码率并发上限: {links_limit} 路, '
            f'空闲超 {LINK_IDLE_TIMEOUT}s 释放配额, 换台防抖: {float(args.zap_debounce)}s)')

    engine_args = argparse.Namespace(
        timeout=float(args.timeout), insecure_tls=False, cache_ttl=60.0, playlist_cache_ttl=2.0,
        refresh_interval=1.0, control_step_jitter_min_ms=0, control_step_jitter_max_ms=0,
        heartbeat_interval=30.0, session_ttl=7200.0,
        meta_json=os.path.join(data_dir, 'proxy-cache-state-rs.json'),
        device_json=os.path.join(data_dir, 'device-state-rs.json'),
        links_per_device=links_limit,
        zap_debounce=float(args.zap_debounce))   # 原版漏传该字段, --zap-debounce / YSP_ZAP_DEBOUNCE 实际不生效
    resolve_paths(engine_args)
    resolver = Resolver(engine_args)
    if not args.no_4k:
        resolver.start_heartbeat()
        threading.Thread(target=init_resolver, daemon=True, name='engine-init').start()

    srv = Server((args.bind, args.port), Handler)
    uniq = global_channel_dir.unique_channels()
    c_yangshi = sum(1 for c in uniq if c['group'] == '央视')
    c_weishi = sum(1 for c in uniq if c['group'] == '卫视')
    RED_BOLD = '\033[1;31m'
    RESET = '\033[0m'
    log('====================================================================')
    log(f'ysp-live v{__version__} 启动成功: {len(uniq)} 个独立频道 (央视 {c_yangshi} 路, 卫视 {c_weishi} 路)')
    log(f'全频道订阅:   http://localhost:{args.port}/all.m3u')
    log(f'系统健康度:   http://localhost:{args.port}/health')
    log(f'实时诊断日志: http://localhost:{args.port}/diag')
    log(f'{RED_BOLD}--------------------------------------------------------------------{RESET}')
    log(f'{RED_BOLD}[官方正版] 首发地址：https://t.me/garysclub{RESET}')
    log(f'{RED_BOLD}[官方正版] 首发频道：https://t.me/garysclubchannel{RESET}')
    log(f'{RED_BOLD}[防骗警告] 其他任何渠道均非作者发布！更没有在恩山论坛和QQ群发布过！{RESET}')
    log(f'{RED_BOLD}===================================================================={RESET}')
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        log('[系统] 服务已停止')
    finally:
        stop_companion_engine()


if __name__ == '__main__':
    main()
