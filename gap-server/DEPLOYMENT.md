# GAP Server Deployment Guide

This document describes how to deploy the GAP server as a persistent daemon on a Sprite and expose it to the internet.

## Prerequisites

- Sprite CLI installed and configured
- A sprite created (e.g., `gap-test`)
- GAP binary built and available at `gap-src/gap-4.15.1/gap` on the sprite

## Deployment Steps

### 1. Copy gap_server.py to the Sprite

```bash
sprite -s gap-test exec sh -c "cat > gap_server.py" << 'EOF'
[paste contents of gap_server.py here]
EOF
```

Alternatively, use a heredoc as shown in the actual deployment.

### 2. Start the Server as a Daemon

The sprite's public URL routes traffic to port 8080, so the server must listen on that port:

```bash
sprite -s gap-test exec sh -c 'GAP_SERVER_PORT=8080 python3 gap_server.py > gap_server.log 2>&1 &'
```

**Important notes:**
- The server must listen on port 8080 (not 8000 or other ports)
- Use `&` to run in background
- Redirect output to a log file for debugging
- Set `GAP_SERVER_PORT=8080` environment variable

### 3. Make the Sprite URL Public

```bash
sprite -s gap-test url update --auth public
```

This removes authentication requirements and makes the sprite accessible to the internet.

### 4. Get the Public URL

```bash
sprite -s gap-test url
```

This will show the public URL (e.g., `https://gap-test-bmhkf.sprites.app`)

## Testing

Test locally on the sprite:
```bash
sprite -s gap-test exec curl -s -X POST -d "1+1;" http://localhost:8080
```

Test via the public URL:
```bash
curl -s -X POST -d "1+1;" https://gap-test-bmhkf.sprites.app
```

Both should return `2`.

## Management Commands

### Check if the server is running
```bash
sprite -s gap-test exec ps aux | grep gap_server
```

### View server logs
```bash
sprite -s gap-test exec cat gap_server.log
```

### Stop the server
```bash
sprite -s gap-test exec pkill -9 -f gap_server.py
```

### Restart the server
```bash
sprite -s gap-test exec pkill -9 -f gap_server.py
sprite -s gap-test exec sh -c 'GAP_SERVER_PORT=8080 python3 gap_server.py > gap_server.log 2>&1 &'
```

## Key Points

1. **Port 8080 is required** - The sprite's public URL proxy routes to port 8080
2. **Background execution** - Use `&` to keep the process running after the sprite exec command ends
3. **Public authentication** - Use `sprite url update --auth public` to allow internet access
4. **No screen/tmux needed** - Simple backgrounding with `&` is sufficient for persistence

## Example Usage

```bash
# Simple arithmetic
curl -s -X POST -d "2+3;" https://gap-test-bmhkf.sprites.app
# Returns: 5

# Factorial
curl -s -X POST -d "Factorial(5);" https://gap-test-bmhkf.sprites.app
# Returns: 120

# Multiple commands
curl -s -X POST -d "x := 10; y := 20; x + y;" https://gap-test-bmhkf.sprites.app
# Returns: 30
```
