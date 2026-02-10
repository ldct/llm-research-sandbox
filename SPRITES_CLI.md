# Sprites CLI (`sprite`)

CLI for managing [sprites.dev](https://sprites.dev) environments — lightweight VMs on Fly.io.

Installed at `~/.local/bin/sprite`.

## Quick Reference

### Listing & Info

```bash
sprite list                    # List all sprites (alias: ls)
sprite url -s <name>           # Show sprite's public URL and auth setting
```

### Creating & Destroying

```bash
sprite create <name>           # Create a new sprite
sprite destroy -force <name>   # Destroy a sprite (skip confirmation)
```

> Without `-force`, `destroy` prompts interactively — which can hang in
> non-interactive shells. Always use `-force` in scripts or from agents.

### Running Commands

```bash
sprite exec -s <name> -- <cmd>   # Run a command remotely (alias: x)
sprite console -s <name>         # Open an interactive shell (alias: c)
```

Example:

```bash
sprite exec -s gap -- uname -a
sprite exec -s gap -- free -h
```

### Checkpoints

```bash
sprite checkpoint list -s <name>           # List checkpoints (alias: ls)
sprite checkpoint create -s <name>         # Create a checkpoint
sprite checkpoint info <id> -s <name>      # Show checkpoint details
sprite restore <id> -s <name>              # Restore from a checkpoint
```

### Port Forwarding

```bash
sprite proxy <port1> [port2...]   # Forward local ports through remote proxy
```

### URL Auth

```bash
sprite url update --auth public -s <name>   # Make URL publicly accessible
sprite url update --auth sprite -s <name>   # Require sprite auth
```

### Directory Binding

```bash
sprite use <name>   # Bind a sprite to the current directory (creates .sprite file)
                    # After this, -s flag is optional when working in that directory
```

## Global Flags

| Flag | Description |
|------|-------------|
| `-s <name>` / `--sprite <name>` | Specify which sprite |
| `-o <name>` / `--org <name>` | Specify organization |
| `--debug[=<file>]` | Enable debug logging |

## Typical Sprite Specs

From testing, a sprite VM typically has:
- **CPU**: AMD EPYC, 8 cores @ 2GHz
- **RAM**: ~8 GiB
- **Disk**: ~99 GB
- **OS**: Linux (Fly.io kernel)

## Current Sprites

- `gap` — https://gap-bmhkf.sprites.app (public)
- `gap-test` — https://gap-test-bmhkf.sprites.app (public)
