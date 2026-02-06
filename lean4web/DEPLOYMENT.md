# Lean4web Deployment Guide (exe.dev)

This document describes how to deploy lean4web on an exe.dev VM.

## Prerequisites

- exe.dev VM with sufficient disk space (~12GB recommended)
- Git installed

## Deployment Steps

### 1. Clone the Repository

```bash
cd /home/exedev
git clone https://github.com/ldct/llm-research-sandbox
cd llm-research-sandbox/lean4web
```

### 2. Install Elan and Lean

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
source ~/.elan/env
elan install leanprover/lean4:v4.24.0
elan default leanprover/lean4:v4.24.0
```

### 3. Update Lake Dependencies (for Lean4270 project)

```bash
cd Projects/Lean4270
source ~/.elan/env && lake update
cd ../..  # back to lean4web root
```

This downloads the mathlib cache (~6GB).

### 4. Install Node.js 25.x

The project requires Node.js 25.x:

```bash
# Install Node.js 20 first (for npm/n)
curl -fsSL https://deb.nodesource.com/setup_20.x | sudo -E bash -
sudo apt-get install -y nodejs

# Use n to install Node.js 25
sudo npm install -g n
sudo n 25
hash -r  # refresh shell path
node --version  # should show v25.x
```

### 5. Install npm Dependencies and Build

```bash
npm install
npm run build
```

### 6. Run in Production Mode

Bubblewrap (sandboxing) is typically not available on exe.dev VMs, so run with:

```bash
source ~/.elan/env && ALLOW_NO_BUBBLEWRAP=true npm run production
```

The server runs on port 8080 by default.

### 7. Access the Application

The app is available at: `https://<your-vm>.exe.xyz:8080/`

## Configuration Notes

### Default Project

The default project is configured in `client/src/store/project-atoms.ts`:

```typescript
const DEFAULT_PROJECT = 'Lean4270'
```

If you change this, rebuild the client:

```bash
npm run build:client
```

### Available Projects

Projects are stored in `Projects/` directory:
- `Lean4270` - Uses Lean 4.24.0 with mathlib
- `Stable` - Uses Lean 4.24.0 with mathlib

Each project has its own `lean-toolchain` file specifying the Lean version.

## Running as a Systemd Service

For persistent deployment, create a systemd service:

```bash
sudo tee /etc/systemd/system/lean4web.service << 'EOF'
[Unit]
Description=Lean4web Server
After=network.target

[Service]
Type=simple
User=exedev
WorkingDirectory=/home/exedev/llm-research-sandbox/lean4web
Environment="PATH=/home/exedev/.elan/bin:/usr/local/bin:/usr/bin:/bin"
Environment="ALLOW_NO_BUBBLEWRAP=true"
Environment="NODE_ENV=production"
ExecStart=/usr/local/bin/node server/index.mjs
Restart=on-failure

[Install]
WantedBy=multi-user.target
EOF

sudo systemctl daemon-reload
sudo systemctl enable lean4web
sudo systemctl start lean4web
```

Manage with:
```bash
sudo systemctl status lean4web
sudo systemctl restart lean4web
journalctl -u lean4web -f
```

## Troubleshooting

### "lake: command not found"

Ensure elan is in the PATH:
```bash
source ~/.elan/env
```

### "Bubblewrap is not available"

Set the environment variable:
```bash
export ALLOW_NO_BUBBLEWRAP=true
```

### Server crashes on first request

Check that the default project exists in `Projects/` and has been built with `lake update`.

### Disk space issues

The mathlib cache is ~6GB. Check usage with:
```bash
df -h
du -sh /home/exedev/*
```

## Disk Usage

Typical deployment uses:
- Lean/elan toolchain: ~500MB
- Mathlib cache: ~6GB
- Node modules: ~500MB
- Total: ~7-8GB
