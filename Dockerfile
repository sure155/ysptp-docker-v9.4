FROM python:3.12-alpine
ENV TZ=Asia/Shanghai     PYTHONUNBUFFERED=1     YSP_DATA_DIR=/app/data
RUN apk add --no-cache nodejs tzdata ca-certificates &&     cp /usr/share/zoneinfo/Asia/Shanghai /etc/localtime &&     echo "Asia/Shanghai" > /etc/timezone &&     mkdir -p /app /app/data
WORKDIR /app
COPY ysp_live.py /app/ysp_live.py
COPY ysp-engine.js /app/ysp-engine.js
EXPOSE 8767
VOLUME ["/app/data"]
CMD ["python3", "/app/ysp_live.py", "8767", "--no-4k"]
