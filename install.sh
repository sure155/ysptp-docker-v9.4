#!/bin/bash
# ysp-live v9.4 一键部署脚本
# 先低码 1080P → 停留后自动升高码率；VPS 场景优化版
# --no-4k：海外 VPS 设备协议注册失败时自动回退 1080p，避免高码率超时报错
set -e

REPO_URL="https://github.com/sure155/ysptp-docker-v9.4.git"
TARGET_DIR="/opt/ysp-live-v9.4"

echo ">>> 拉取 sure155/ysptp-docker-v9.4 项目..."
rm -rf "$TARGET_DIR"
git clone --depth 1 "$REPO_URL" "$TARGET_DIR"
cd "$TARGET_DIR"

echo ">>> 清理可能残留的旧容器..."
docker rm -f ysp-live-v9.4 ysp-live 2>/dev/null; true

echo ">>> 构建并启动容器..."
docker compose build --no-cache
docker compose up -d

echo ">>> 等待引擎就绪（约 10~20 秒）..."
sleep 10

IP=$(curl -s --max-time 5 ifconfig.me 2>/dev/null || hostname -I | awk '{print $1}')
echo ""
echo "ysp-live v9.4 已部署完毕"
echo "订阅地址: http://$IP:8767/all.m3u"
echo "节目单订阅: http://$IP:8767/epg.xml"
echo "实时诊断: http://$IP:8767/diag"
echo "查看日志: docker logs -f ysp-live-v9.4"
echo ""
echo "常用命令:"
echo "  启动/更新: cd /opt/ysp-live-v9.4 && docker compose up -d --build"
echo "  查看日志:  docker logs -f ysp-live-v9.4"
echo "  重启:      docker compose restart"
echo "  卸载:      cd /opt/ysp-live-v9.4 && docker compose down -v && cd /opt && rm -rf ysp-live-v9.4"
