# Firecracker MicroVM on macOS (Apple Silicon) - Setup Notes

## Architecture

```
macOS (M5 Max) → Lima VM (Ubuntu, nested virtualization) → Firecracker → MicroVM (Ubuntu 24.04)
```

Firecracker requires Linux with KVM, so on macOS we use Lima as a bridge.

## Prerequisites

```bash
brew install lima
```

## Step 1: Start Lima VM with nested virtualization

```bash
limactl start --set '.nestedVirtualization=true' --name=mvm template:default
```

This downloads an Ubuntu cloud image and starts a VM with KVM support.

## Step 2: Install Firecracker inside Lima VM

```bash
limactl shell mvm -- bash -c '
FC_VERSION="v1.13.0"
ARCH="aarch64"
cd /tmp
wget -q https://github.com/firecracker-microvm/firecracker/releases/download/${FC_VERSION}/firecracker-${FC_VERSION}-${ARCH}.tgz
tar -xzf firecracker-${FC_VERSION}-${ARCH}.tgz
sudo mv release-${FC_VERSION}-${ARCH}/firecracker-${FC_VERSION}-${ARCH} /usr/local/bin/firecracker
sudo chmod +x /usr/local/bin/firecracker
'
```

## Step 3: Download kernel and rootfs

```bash
limactl shell mvm -- bash -c '
ARCH="aarch64"
mkdir -p ~/firecracker-demo && cd ~/firecracker-demo

# Kernel
latest_kernel_key=$(wget "http://spec.ccfc.min.s3.amazonaws.com/?prefix=firecracker-ci/v1.13/${ARCH}/vmlinux-5.10&list-type=2" -O - 2>/dev/null | grep -oP "(?<=<Key>)(firecracker-ci/v1.13/${ARCH}/vmlinux-5\.10\.[0-9]{3})(?=</Key>)")
wget -q "https://s3.amazonaws.com/spec.ccfc.min/${latest_kernel_key}" -O vmlinux-5.10

# Ubuntu rootfs (squashfs)
latest_ubuntu_key=$(curl -s "http://spec.ccfc.min.s3.amazonaws.com/?prefix=firecracker-ci/v1.13/${ARCH}/ubuntu-&list-type=2" | grep -oP "(?<=<Key>)(firecracker-ci/v1.13/${ARCH}/ubuntu-[0-9]+\.[0-9]+\.squashfs)(?=</Key>)" | sort -V | tail -1)
ubuntu_version=$(basename $latest_ubuntu_key .squashfs | grep -oE "[0-9]+\.[0-9]+")
wget -q -O ubuntu-${ubuntu_version}.squashfs.upstream "https://s3.amazonaws.com/spec.ccfc.min/$latest_ubuntu_key"
'
```

## Step 4: Convert squashfs to ext4 and configure

```bash
limactl shell mvm -- bash -c '
cd ~/firecracker-demo
sudo apt-get install -y squashfs-tools

# Extract squashfs
sudo unsquashfs -d /tmp/ubuntu-rootfs ubuntu-24.04.squashfs.upstream

# Generate SSH key
ssh-keygen -t rsa -f ubuntu-24.04.id_rsa -N ""

# Add SSH key to rootfs
sudo mkdir -p /tmp/ubuntu-rootfs/root/.ssh
sudo cp ubuntu-24.04.id_rsa.pub /tmp/ubuntu-rootfs/root/.ssh/authorized_keys
sudo chmod 700 /tmp/ubuntu-rootfs/root/.ssh
sudo chmod 600 /tmp/ubuntu-rootfs/root/.ssh/authorized_keys

# Set root password
echo "root:root" | sudo chpasswd -R /tmp/ubuntu-rootfs

# IMPORTANT: Replace the fcnet-setup.sh with static IP config
# The upstream script tries to derive IP from MAC address using a specific format
# that does not work with standard 6-octet MACs for arbitrary IPs
sudo bash -c "cat > /tmp/ubuntu-rootfs/usr/local/bin/fcnet-setup.sh" << "EOF"
#!/usr/bin/env bash
ip addr add 172.16.0.2/30 dev eth0
ip link set eth0 up
ip route add default via 172.16.0.1
EOF
sudo chmod +x /tmp/ubuntu-rootfs/usr/local/bin/fcnet-setup.sh

# Create ext4 image
dd if=/dev/zero of=ubuntu-24.04.ext4 bs=1M count=512
mkfs.ext4 ubuntu-24.04.ext4
sudo mkdir -p /tmp/ext4mount
sudo mount ubuntu-24.04.ext4 /tmp/ext4mount
sudo cp -a /tmp/ubuntu-rootfs/* /tmp/ext4mount/
sudo umount /tmp/ext4mount
'
```

## Step 5: Launch the MicroVM

Run this all as root inside the Lima VM:

```bash
limactl shell mvm -- sudo bash -c '
cd /home/$(whoami).linux/firecracker-demo

# Setup TAP networking
ip link del tap0 2>/dev/null || true
ip tuntap add dev tap0 mode tap
ip addr add 172.16.0.1/30 dev tap0
ip link set dev tap0 up
echo 1 > /proc/sys/net/ipv4/ip_forward
iptables -P FORWARD ACCEPT
HOST_IFACE=$(ip -j route list default | jq -r ".[0].dev")
iptables -t nat -D POSTROUTING -o "$HOST_IFACE" -j MASQUERADE 2>/dev/null || true
iptables -t nat -A POSTROUTING -o "$HOST_IFACE" -j MASQUERADE

# Start Firecracker
rm -f /tmp/firecracker.socket
firecracker --api-sock /tmp/firecracker.socket &
sleep 1

# Configure via API
API=/tmp/firecracker.socket
curl --unix-socket $API -s -X PUT http://localhost/boot-source \
  -H "Content-Type: application/json" \
  -d "{\"kernel_image_path\": \"./vmlinux-5.10\", \"boot_args\": \"console=ttyS0 reboot=k panic=1 pci=off\"}"

curl --unix-socket $API -s -X PUT http://localhost/drives/rootfs \
  -H "Content-Type: application/json" \
  -d "{\"drive_id\": \"rootfs\", \"path_on_host\": \"./ubuntu-24.04.ext4\", \"is_root_device\": true, \"is_read_only\": false}"

curl --unix-socket $API -s -X PUT http://localhost/network-interfaces/eth0 \
  -H "Content-Type: application/json" \
  -d "{\"iface_id\": \"eth0\", \"guest_mac\": \"AA:FC:00:00:00:01\", \"host_dev_name\": \"tap0\"}"

curl --unix-socket $API -s -X PUT http://localhost/machine-config \
  -H "Content-Type: application/json" \
  -d "{\"vcpu_count\": 2, \"mem_size_mib\": 256}"

curl --unix-socket $API -s -X PUT http://localhost/actions \
  -H "Content-Type: application/json" \
  -d "{\"action_type\": \"InstanceStart\"}"
'
```

## Step 6: SSH into the MicroVM

Wait ~10 seconds for boot, then:

```bash
limactl shell mvm -- bash -c '
ssh -i ~/firecracker-demo/ubuntu-24.04.id_rsa -o StrictHostKeyChecking=no root@172.16.0.2
'
```

## Gotchas / Debugging Notes

### 1. The fcnet-setup.sh MAC-to-IP script doesn't work for custom IPs
The upstream Firecracker CI rootfs includes `/usr/local/bin/fcnet-setup.sh` which derives
the guest IP from the MAC address. It expects a specific MAC format with `06:00:` prefix
and converts the remaining octets to IP. This doesn't work for arbitrary IP assignments
with standard 6-octet MACs. **Solution**: Replace the script with a static IP configuration.

### 2. MAC address must be exactly 6 octets
Firecracker validates MAC addresses strictly. `AA:FC:06:00:AC:10:00:02` (8 octets) is
rejected as invalid. Use standard 6-octet format like `AA:FC:00:00:00:01`.

### 3. Ubuntu 24.04 uses netplan, not /etc/network/interfaces
The squashfs image from Firecracker CI doesn't have `/etc/network/interfaces` directory.
However, the `fcnet.service` systemd unit handles networking via the fcnet-setup.sh script,
so netplan/interfaces config is not needed if you fix the script.

### 4. All Firecracker commands must run as root
The firecracker binary, TAP setup, and API socket all require root. Run everything under
`sudo` within the Lima VM.

### 5. Boot takes ~3-5 seconds to full SSH readiness
The kernel boots in ~3s, systemd services complete in ~8s, and SSH is ready shortly after.
The first ping may have high latency (~1s) while the network initializes.

## Cleanup

```bash
# Stop the Lima VM (stops Firecracker too)
limactl stop mvm

# Delete everything
limactl delete mvm
```

## Snapshot and Restore

Firecracker supports pausing a VM, snapshotting its full state to disk, and restoring
it in a completely new Firecracker process.

### Create a snapshot

```bash
# Write something to the VM so we can verify restore
limactl shell mvm -- ssh -i ~/firecracker-demo/ubuntu-24.04.id_rsa root@172.16.0.2 \
  "echo MY_MARKER > /tmp/marker.txt"

# Pause, snapshot, resume (all as root inside Lima)
limactl shell mvm -- sudo bash -c '
API=/tmp/firecracker.socket
cd /home/xuanji.linux/firecracker-demo
mkdir -p ./snapshots

curl --unix-socket $API -s -X PATCH http://localhost/vm \
  -H "Content-Type: application/json" -d "{\"state\": \"Paused\"}"

curl --unix-socket $API -s -X PUT http://localhost/snapshot/create \
  -H "Content-Type: application/json" \
  -d "{\"snapshot_type\": \"Full\", \"snapshot_path\": \"./snapshots/snapshot_file\", \"mem_file_path\": \"./snapshots/mem_file\"}"

curl --unix-socket $API -s -X PATCH http://localhost/vm \
  -H "Content-Type: application/json" -d "{\"state\": \"Resumed\"}"
'
```

Produces: `snapshot_file` (12K device state) + `mem_file` (256MB memory).

### Restore from snapshot

```bash
limactl shell mvm -- sudo bash -c '
cd /home/xuanji.linux/firecracker-demo

# Kill old Firecracker
kill $(pgrep firecracker); sleep 1

# Recreate TAP device (must exist at same name)
ip link del tap0 2>/dev/null || true
ip tuntap add dev tap0 mode tap
ip addr add 172.16.0.1/30 dev tap0
ip link set dev tap0 up

# Start fresh Firecracker
API=/tmp/firecracker.socket; rm -f $API
firecracker --api-sock $API &
sleep 1

# Load snapshot
curl --unix-socket $API -s -X PUT http://localhost/snapshot/load \
  -H "Content-Type: application/json" \
  -d "{\"snapshot_path\": \"./snapshots/snapshot_file\", \"mem_backend\": {\"backend_path\": \"./snapshots/mem_file\", \"backend_type\": \"File\"}, \"enable_diff_snapshots\": false}"

# Resume
curl --unix-socket $API -s -X PATCH http://localhost/vm \
  -H "Content-Type: application/json" -d "{\"state\": \"Resumed\"}"
'
```

### Restore performance (observed)

- Snapshot load: **5.3ms**
- VM resume: **0.6ms**
- Total time to restored + running VM: **~6ms**
- All guest state (files, processes, memory) preserved across kill + restore

### Important notes

- TAP device and disk files must exist at the same paths when restoring
- Network connections may not survive (SSH reconnect needed)
- Restoring the same snapshot multiple times is fine for this project (Firecracker warns about
  crypto/entropy duplication, but that's not a concern here)
- Guest clock continues from snapshot point (may need NTP resync)

## Disk I/O Performance (Nested Virtualization)

Firecracker's virtio block device has severe I/O overhead under nested virtualization
(macOS → Lima VM → Firecracker). Each VMExit in the inner VM triggers a nested VMExit
through the outer hypervisor.

### Benchmark: 50MB sequential read (cold cache)

| Config | Time | vs Lima |
|--------|------|---------|
| Lima (direct) | 0.013s | 1x |
| FC default (MMIO, sync io) | 13.3s | ~1000x |
| FC + `--enable-pci` + `io_engine: Async` | 2.3s | ~170x |
| FC + PCI + io_uring + warm host cache | 1.7s | ~130x |

### Tuning options applied

1. **`--enable-pci`** on firecracker launch (reduces VMExits vs MMIO transport)
2. **Remove `pci=off`** from boot args
3. **`"io_engine": "Async"`** in drive config (io_uring, up to 30x IOPS improvement)
4. **`"cache_type": "Unsafe"`** (skip fsync, fine for dev)
5. **Warm host page cache** before boot: `cat rootfs.ext4 > /dev/null`

### Impact on Mathlib

`import Mathlib` reads ~5GB of olean files:
- In container (Lima, no Firecracker, cold): **~20 seconds**
- In container (warm disk cache): **~5 seconds**
- In Firecracker (nested virt, even with tmpfs): **30+ minutes**

The slowdown is NOT purely I/O. Even with all oleans copied to tmpfs inside the VM
(zero disk reads confirmed via /proc/PID/io), the import takes 30+ min. The overhead
appears to be from nested virtualization affecting CPU-intensive olean deserialization —
every syscall and page fault goes through two layers of hypervisor.

### Tmpfs workaround (partially effective)

Copying the .lake directory to tmpfs inside the VM eliminates the disk I/O bottleneck
but doesn't fix the CPU overhead:

```bash
# Inside the Firecracker VM:
mkdir -p /tmp/fast-project
mount -t tmpfs -o size=8G tmpfs /tmp/fast-project
cp -a /project/* /tmp/fast-project/   # ~10 min for 7GB over virtio
cp -a /project/.lake /tmp/fast-project/.lake
cd /tmp/fast-project
# Import still takes 30+ min due to nested virt CPU overhead
```

### Snapshot/Restore Results (Mathlib.Data.Nat.Basic)

Successfully tested with a smaller import (`import Mathlib.Data.Nat.Basic`):

| Step | Time |
|------|------|
| One-time import | 40 min (2393s) |
| Snapshot creation (4GB memory) | 14.5s |
| Snapshot load | 7.6ms |
| VM resume | 0.3ms |
| **Total restore** | **~30ms** |

The VM, SSH, and all processes came back alive after restore. However, the REPL's
stdin/stdout pipes between Python and the repl binary did not survive the restore —
queries sent to the HTTP API hang. This is a known challenge with snapshotting
inter-process communication state.

**Potential fixes:**
- Have the HTTP server detect stale pipes and re-establish them
- Snapshot only the bare repl process (no HTTP wrapper)
- Use a single-process architecture where the HTTP server IS the repl
- On bare-metal Linux (no nested virt), the import would be fast enough (~20s)
  that re-importing after restore is viable

### Full `import Mathlib` — NOT viable under nested virt

Multiple attempts to import all of Mathlib in Firecracker on macOS failed:
- Process consistently crashes or gets stuck around 3-5GB RSS
- VM becomes unresponsive (SSH/ping timeout) under memory pressure
- Even with 12GB RAM and 8 CPUs, the import does not complete
- Root cause: combination of 130-1000x I/O overhead + nested virt CPU overhead

### Recommendation

For macOS + Apple Silicon development, Firecracker's nested virtualization makes
heavy workloads like full `import Mathlib` impractical. Options:
1. **Use containers directly** (nerdctl/Docker in Lima) — 20s full import, works great
2. **Use Firecracker on bare-metal Linux** — should be close to container speed
3. **Partial imports work** — `import Mathlib.Data.Nat.Basic` succeeds in ~40 min
4. **Snapshot/restore is fast** (~30ms) but REPL pipes need engineering to survive

## Lean4web / Mathlib REPL in Firecracker

### Building the rootfs

The rootfs is extracted from the `ghcr.io/ldct/mathlib4-repl:v4.27.0` Docker image (arm64).
Since this is a minimal container image without systemd or sshd, a custom `/sbin/init`
script is needed:

```bash
#!/bin/bash
mount -t proc proc /proc
mount -t sysfs sys /sys
mount -t devtmpfs dev /dev 2>/dev/null
mkdir -p /dev/pts && mount -t devpts devpts /dev/pts
ip addr add 172.16.0.2/30 dev eth0
ip link set eth0 up
ip route add default via 172.16.0.1
echo "nameserver 8.8.8.8" > /etc/resolv.conf
mkdir -p /run/sshd
/usr/sbin/sshd
exec /bin/bash
```

openssh-server and iproute2 must be installed into the rootfs via chroot.

### Launching the REPL

```bash
ssh root@172.16.0.2 "
  export PATH=/root/.elan/bin:\$PATH
  cd /project
  nohup python3 /repl_server.py > /tmp/repl.log 2>&1 &
"
```

### Resource requirements

- 12GB+ RAM (Mathlib import peaks at ~5.4GB RSS)
- 8 CPUs recommended
- 15GB rootfs (11GB used by Mathlib oleans + toolchain)
- Lima VM: 16GB RAM, 8 CPUs

## Performance Observed (2026-03-24, M5 Max)

- Kernel boot: ~3 seconds
- Full systemd boot to SSH ready: ~10 seconds
- Memory usage in guest: ~31MB used of 221MB allocated
- Ping latency (after warmup): 0.5ms
- Snapshot restore: ~6ms
- CPU overhead (nested virt): ~1.2x
- Disk I/O overhead (nested virt): ~130-1000x
- Guest: Ubuntu 24.04.2 LTS, Linux 5.10.239, aarch64, 2-8 vCPUs
