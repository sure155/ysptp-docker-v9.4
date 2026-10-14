#!/usr/bin/env python3
"""
对照校验: 比较「原版脚本」和「优化版脚本」的协议关键内容是否逐项一致。

用法:
    python3 verify_against_original.py 原版.py ysp_live.py

校验内容 (任何一项不一致都会列出并以非 0 退出):
  1. 协议常量: AK / RSA 公钥 / 各接口 URL / JCE 版本号 / cKey 密钥 …
  2. 频道表: 设备协议频道 ID、DEFAULT_CHANNELS、别名、TVG-ID、时移/高码率/强制备用集合
  3. 设备资料池: 优化版把 53 条设备资料压缩成元组, 这里展开后必须与原版逐字段一致
  4. 确定性函数: 固定随机数 / 时间 / UUID 后, 比较
        compute_x_uid / compute_fingerprint / java hash / 报文构造 /
        AES-GCM / RSA-OAEP / JCE 打包 (_wrap) / cKey 生成 (_ckey) / 时移参数解析 …
  不比较的内容: 播放列表代理 URL (优化版加了 HMAC 签名, 有意不同)。
"""
import contextlib
import dataclasses
import importlib.util
import itertools
import sys
import time
import uuid


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


@contextlib.contextmanager
def deterministic():
    """固定 os.urandom / secrets.token_bytes / secrets.randbits / uuid4 / time.time, 每次进入都从头开始。"""
    import os
    import secrets
    counter = itertools.count(1)

    def fake_urandom(n):
        return bytes(((next(counter) * 37) & 0xFF) for _ in range(n))

    saved = (os.urandom, secrets.token_bytes, secrets.randbits, uuid.uuid4, time.time)
    os.urandom = fake_urandom
    secrets.token_bytes = fake_urandom
    secrets.randbits = lambda k: (next(counter) * 2654435761) & ((1 << k) - 1)
    uuid.uuid4 = lambda: uuid.UUID(int=(next(counter) * 0x9E3779B97F4A7C15) & ((1 << 128) - 1), version=4)
    time.time = lambda: 1_750_000_000.123
    try:
        yield
    finally:
        os.urandom, secrets.token_bytes, secrets.randbits, uuid.uuid4, time.time = saved


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    old = load(sys.argv[1], 'old_ysp')
    new = load(sys.argv[2], 'new_ysp')
    failures = []
    checked = 0

    def same(label, a, b):
        nonlocal checked
        checked += 1
        if a != b:
            failures.append(label)
            print(f'  ✗ {label}\n      原版: {str(a)[:160]}\n      新版: {str(b)[:160]}')

    # 1. 常量 -----------------------------------------------------------
    const_names = [
        'AK', 'RSA_PUBLIC_KEY_B64', 'CLOUD_GET_URL', 'CLOUD_REGISTER_URL', 'APP_START_URL', 'DRM_CONFIG_URL',
        'VERSION_CONFIG_URL', 'DICTIONARY_URL', 'INDEX_URL', 'REPORT_SINGLE_URL', 'COLLECT_REPORT_URL',
        'LIVE_V1_01_URL', 'LIVE_V1_02_URL', 'VDN_GETSTREAM_URL', 'DEFAULT_LIVE_USER_ID', 'DEFAULT_DEVICE_NAME',
        'VDN_APP_NAME', 'REPORT_APP_KEY', 'COLLECT_SDK_VERSION', 'DEFAULT_PAGE_NAME', 'DEFAULT_ACCEPT_LANGUAGE',
        'RESULT_OK', 'RESULT_NEEDS_REGISTER', 'RESULT_GET_MISSING_OR_INVALID', 'RESULT_REGISTERED_ELSEWHERE',
        'RESULT_REGISTER_RETRY_LATER', 'VER_NAME', 'VER_CODE', 'APP_ID', 'QMF_APP_ID', 'QMF_PLATFORM', 'BIZ_ID',
        'CHAN_ID', '_CK_PLATFORM', '_CK_APPVER', '_CK_TEA', '_CK_GTEA', '_CK_XOR', '_CK_GXOR', '_BK_H264',
        'LOGO_BASE', 'UA', 'WINDOW', 'MAX_SEGS', 'BK_URL_TTL', 'REFRESH_INTERVAL', 'LINK_IDLE_TIMEOUT',
        '_SBOX', '_RCON', 'AUTHOR_COMMUNITY', 'AUTHOR_CHANNEL',
    ]
    print('[1/4] 协议常量')
    for n in const_names:
        same(n, getattr(old, n), getattr(new, n))

    # 2. 频道表 ---------------------------------------------------------
    print('[2/4] 频道表')
    same('channels()', old.channels(), new.channels())
    for n in ('DEFAULT_CHANNELS', 'ALIAS_MAP', 'TVG_IDS', 'TIMESHIFT_SUPPORTED', 'BACKEND_CHANNELS', 'FORCE_BK',
              'TRUE_4K_CHANNELS'):
        same(n, getattr(old, n), getattr(new, n))

    # 3. 设备资料池 -------------------------------------------------------
    print('[3/4] 设备资料池 (展开后逐项对比)')
    same('DEVICE_PROFILE_POOL 条数', len(old.DEVICE_PROFILE_POOL), len(new.DEVICE_PROFILE_POOL))
    same('DEVICE_PROFILE_POOL 内容与顺序', old.DEVICE_PROFILE_POOL, new.DEVICE_PROFILE_POOL)
    for i, (to, tn) in enumerate(zip(old.DEVICE_PROFILE_POOL, new.DEVICE_PROFILE_POOL)):
        po = old.device_profile_from_template(to, 'a' * 16, 'aa:bb:cc:dd:ee:ff')
        pn = new.device_profile_from_template(tn, 'a' * 16, 'aa:bb:cc:dd:ee:ff')
        same(f'pool[{i}] {to["model"]} 生成的 DeviceProfile', dataclasses.asdict(po), dataclasses.asdict(pn))
        same(f'pool[{i}] {to["model"]} 的 x_uid', old.compute_x_uid(po), new.compute_x_uid(pn))

    # 4. 确定性函数 -------------------------------------------------------
    print('[4/4] 确定性函数 (固定随机数/时间)')
    for s in ('', 'hello', '1698mt5895Sony', 'XR-85Z9K'):
        same(f'java_string_hashcode({s!r})', old.java_string_hashcode(s), new.java_string_hashcode(s))
    same('java_uuid_from_hashes', old.java_uuid_from_hashes(-12345, 987654321), new.java_uuid_from_hashes(-12345, 987654321))
    for t in (0, 1_700_000_000, 1_750_000_000):
        same(f'native_day0_ms({t})', old.native_day0_ms(t), new.native_day0_ms(t))
    same('compute_fingerprint', old.compute_fingerprint('UID', 1_750_000_000_123), new.compute_fingerprint('UID', 1_750_000_000_123))
    same('compute_vdn_code', old.compute_vdn_code('secret', 'rnd'), new.compute_vdn_code('secret', 'rnd'))
    same('build_vdn_appcommon', old.build_vdn_appcommon('1.4.1'), new.build_vdn_appcommon('1.4.1'))
    same('form_encode', old.form_encode([('a b', '中文*-._~/'), ('k', 'v')]), new.form_encode([('a b', '中文*-._~/'), ('k', 'v')]))
    same('resolution_from_screen_param', [old.resolution_from_screen_param(x) for x in ('7680-4320-280', 'x', '')],
         [new.resolution_from_screen_param(x) for x in ('7680-4320-280', 'x', '')])
    same('sanitize_profile_id', old.sanitize_profile_id('XR-85Z9K / Pro'), new.sanitize_profile_id('XR-85Z9K / Pro'))
    same('normalize_channel', [old.normalize_channel(x) for x in ('/CCTV1.m3u8', 'cctv16(4k)', ' CCTV5 ')],
         [new.normalize_channel(x) for x in ('/CCTV1.m3u8', 'cctv16(4k)', ' CCTV5 ')])
    pl = '#EXTM3U\n#EXTINF:6,\nseg1.ts\r\nhttp://x/y/seg2.ts\n\n'
    same('rewrite_playlist_urls', old.rewrite_playlist_urls(pl, 'http://h/a/b.m3u8'), new.rewrite_playlist_urls(pl, 'http://h/a/b.m3u8'))

    tpl = old.DEVICE_PROFILE_POOL[0]
    po = old.device_profile_from_template(tpl, 'a' * 16, 'aa:bb:cc:dd:ee:ff')
    pn = new.device_profile_from_template(tpl, 'a' * 16, 'aa:bb:cc:dd:ee:ff')
    same('build_report_common_value', old.build_report_common_value(po, 'XU', 'dangbei', '1.4.1', '1.0.0', 1750000000123),
         new.build_report_common_value(pn, 'XU', 'dangbei', '1.4.1', '1.0.0', 1750000000123))
    same('build_app_start_body', old.build_app_start_body(po, 'XU', 'dangbei', '1.4.1', 1750000000123),
         new.build_app_start_body(pn, 'XU', 'dangbei', '1.4.1', 1750000000123))
    same('build_collect_headers', old.build_collect_headers(po), new.build_collect_headers(pn))
    same('compact_json_bytes', old.compact_json_bytes({'u': 'a/b', 'z': 1, 'a': '中'}, True), new.compact_json_bytes({'u': 'a/b', 'z': 1, 'a': '中'}, True))

    key, nonce = bytes(range(32)), bytes(range(12))
    for n in (0, 1, 16, 33, 200):
        pt = bytes((i * 7) & 0xFF for i in range(n))
        same(f'aes_gcm_encrypt(len={n})', old.aes_gcm_encrypt(key, nonce, pt), new.aes_gcm_encrypt(key, nonce, pt))
    with deterministic():
        a = old.aes_gcm_encrypt_b64('hello', 'sessionkey')
    with deterministic():
        b = new.aes_gcm_encrypt_b64('hello', 'sessionkey')
    same('aes_gcm_encrypt_b64', a, b)
    with deterministic():
        a = old.rsa_encrypt_device_id('A' * 40)
    with deterministic():
        b = new.rsa_encrypt_device_id('A' * 40)
    same('rsa_encrypt_device_id (1 块)', a, b)
    with deterministic():
        a = old.rsa_encrypt_device_id('B' * 500)
    with deterministic():
        b = new.rsa_encrypt_device_id('B' * 500)
    same('rsa_encrypt_device_id (多块)', a, b)

    for mod in (old, new):
        mod.GUID = '0123456789abcdef0123456789abcdef'
    with deterministic():
        a = old._wrap(25312, b'body-bytes', 424242)
    with deterministic():
        b = new._wrap(25312, b'body-bytes', 424242)
    same('_wrap (JCE 打包)', a, b)
    wo, wn = old.W(), new.W()
    for w in (wo, wn):
        w.string('pid', 0); w.string('x' * 300, 1); w.long(1 << 40, 2); w.long(5, 3); w.string('fhd', 4)
    same('JCE W 编码', wo.out(), wn.out())
    with deterministic():
        a = old._ckey('2024078201')
    with deterministic():
        b = new._ckey('2024078201')
    same('_ckey (cKey 生成)', a, b)
    with deterministic():
        a = old._ck_guard(1750000000, 'abcdef0123456789')
    with deterministic():
        b = new._ck_guard(1750000000, 'abcdef0123456789')
    same('_ck_guard', a, b)

    with deterministic():
        for q in ('playseek=20250101120000-20250101130000', 'playseek=20250101120000', 'start=1750000000&end=1750003600',
                  'utc=1750000000000', 'x=1', ''):
            same(f'parse_catchup_query({q!r})', old.parse_catchup_query(q), new.parse_catchup_query(q))

    print()
    print(f'共比较 {checked} 项, 不一致 {len(failures)} 项')
    if failures:
        print('不一致项:', ', '.join(failures))
        sys.exit(1)
    print('✓ 全部一致')


if __name__ == '__main__':
    main()
