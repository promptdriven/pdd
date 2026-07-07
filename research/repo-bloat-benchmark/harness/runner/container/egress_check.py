"""Kernel-level egress verification (design §8.1.1 hard tier) — run INSIDE
the runner container before any pilot cell. No API key, no billing: the only
outbound action is a TCP CONNECT handshake check.

Asserts, from inside the runner's network namespace:

1. direct egress is impossible at the kernel level — TCP connects to
   well-known outside addresses fail (the internal Docker network attaches
   no gateway; this is netns/routing enforcement, not env convention);
2. the ACL'd gateway IS reachable (the single sanctioned path);
3. the gateway grants CONNECT to the pinned provider host:443;
4. the gateway REFUSES CONNECT to any other host (ACL enforced);
5. loopback works (the in-process recording proxy needs it).

Exit 0 iff all five hold. Stdlib only.
"""

from __future__ import annotations

import json
import os
import socket
import sys

GATEWAY = os.environ.get("RB_GATEWAY", "gateway:8888")
PROVIDER_HOST = os.environ.get("RB_PROVIDER_HOST", "api.openai.com")
OUTSIDE_PROBES = (("1.1.1.1", 443), ("8.8.8.8", 53))
TIMEOUT = float(os.environ.get("RB_EGRESS_TIMEOUT", "5"))


def _tcp_connect(host: str, port: int) -> bool:
    try:
        with socket.create_connection((host, port), timeout=TIMEOUT):
            return True
    except OSError:
        return False


def _gateway_connect(target_host: str, target_port: int) -> int | None:
    """Issue an HTTP CONNECT through the gateway; return the status code."""
    gw_host, gw_port = GATEWAY.rsplit(":", 1)
    try:
        with socket.create_connection((gw_host, int(gw_port)), timeout=TIMEOUT) as sock:
            request = (
                f"CONNECT {target_host}:{target_port} HTTP/1.1\r\n"
                f"Host: {target_host}:{target_port}\r\n\r\n"
            )
            sock.sendall(request.encode())
            head = sock.recv(1024).decode("latin-1", errors="replace")
        parts = head.split()
        return int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else None
    except OSError:
        return None


def main() -> int:
    checks: dict[str, bool] = {}

    checks["no_direct_egress"] = all(
        not _tcp_connect(host, port) for host, port in OUTSIDE_PROBES
    )

    gw_host, gw_port = GATEWAY.rsplit(":", 1)
    checks["gateway_reachable"] = _tcp_connect(gw_host, int(gw_port))

    provider_status = _gateway_connect(PROVIDER_HOST, 443)
    checks["gateway_allows_pinned_provider"] = provider_status == 200

    blocked_status = _gateway_connect("example.com", 443)
    checks["gateway_blocks_other_hosts"] = blocked_status is not None and (
        blocked_status != 200
    )

    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        probe.listen(1)
        checks["loopback_works"] = _tcp_connect("127.0.0.1", probe.getsockname()[1])

    print(json.dumps(checks, indent=2))
    ok = all(checks.values())
    print("EGRESS LOCKDOWN " + ("VERIFIED" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
