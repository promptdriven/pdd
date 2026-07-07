"""Kernel-level egress verification (design §8.1.1 hard tier).

Run INSIDE the **agent** container before any pilot cell (its namespace is
the one that must be locked down). No API key, no billing: the only outbound
actions are connect/handshake probes.

Asserts, from inside the agent's network namespace:

1. direct egress is impossible at the kernel level across TCP, UDP, and
   IPv6 — connects/sends to well-known outside addresses fail (the agent's
   only network is `internal: true` with no gateway; netns/routing
   enforcement, not env convention). Includes a UDP/53 probe to Docker's
   embedded resolver (127.0.0.11) and a public resolver, closing the
   DNS-tunnel channel `internal: true` does not by itself block;
2. the **gateway is NOT reachable from the agent** — the agent has no
   interface on the proxy-egress network, so it cannot bypass the recording
   proxy by talking to the gateway directly (this is the property the
   previous single-netns topology failed);
3. the **recording proxy IS reachable** on the runner (the single sanctioned
   path to the provider; every byte is recorded there first);
4. loopback works.

The provider-ACL of the gateway itself is verified separately from the
runner's namespace (``--role runner``): gateway grants CONNECT to the pinned
provider host:443 and refuses every other host.

Exit 0 iff all checks for the role hold. Stdlib only.
"""

from __future__ import annotations

import argparse
import json
import os
import socket
import sys

GATEWAY = os.environ.get("RB_GATEWAY", "gateway:8888")
PROVIDER_HOST = os.environ.get("RB_PROVIDER_HOST", "api.openai.com")
# The recording proxy on the runner; the agent addresses it by service name.
PROXY = os.environ.get("RB_PROXY", "runner:8080")
OUTSIDE_TCP_PROBES = (("1.1.1.1", 443), ("8.8.8.8", 53))
# UDP exfil / DNS-tunnel channels: a public resolver and Docker's embedded
# resolver (which forwards external lookups via the daemon even on an
# internal network).
OUTSIDE_UDP_PROBES = (("8.8.8.8", 53), ("1.1.1.1", 53), ("127.0.0.11", 53))
# A public IPv6 literal (Cloudflare DNS) — v6 default routes bypass a
# v4-only lockdown.
OUTSIDE_IPV6_PROBES = (("2606:4700:4700::1111", 443),)
TIMEOUT = float(os.environ.get("RB_EGRESS_TIMEOUT", "5"))
# A minimal DNS query for "example.com" A record (id 0x1234).
_DNS_QUERY = bytes.fromhex(
    "123401000001000000000000076578616d706c6503636f6d0000010001"
)


def _tcp_connect(host: str, port: int, family: int = socket.AF_INET) -> bool:
    try:
        with socket.socket(family, socket.SOCK_STREAM) as sock:
            sock.settimeout(TIMEOUT)
            sock.connect((host, port))
            return True
    except OSError:
        return False


def _udp_dns_reachable(host: str, port: int = 53) -> bool:
    """True iff a DNS query to host:port gets any answer (i.e. egress works)."""
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
            sock.settimeout(TIMEOUT)
            sock.sendto(_DNS_QUERY, (host, port))
            sock.recvfrom(512)
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


def _no_egress_checks() -> dict[str, bool]:
    """Kernel-level egress must be impossible from this namespace."""
    return {
        "no_direct_tcp_egress": all(
            not _tcp_connect(host, port) for host, port in OUTSIDE_TCP_PROBES
        ),
        "no_udp_dns_egress": all(
            not _udp_dns_reachable(host, port) for host, port in OUTSIDE_UDP_PROBES
        ),
        "no_ipv6_egress": all(
            not _tcp_connect(host, port, family=socket.AF_INET6)
            for host, port in OUTSIDE_IPV6_PROBES
        ),
    }


def _loopback_check() -> bool:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        probe.listen(1)
        return _tcp_connect("127.0.0.1", probe.getsockname()[1])


def agent_checks() -> dict[str, bool]:
    """From the AGENT namespace: no egress, gateway unreachable, proxy reachable."""
    checks = _no_egress_checks()
    gw_host, gw_port = GATEWAY.rsplit(":", 1)
    # The agent must NOT be able to reach the gateway (recording-bypass guard).
    checks["gateway_unreachable_from_agent"] = not _tcp_connect(gw_host, int(gw_port))
    # The recording proxy IS the agent's single sanctioned path to the provider.
    proxy_host, proxy_port = PROXY.rsplit(":", 1)
    checks["recording_proxy_reachable"] = _tcp_connect(proxy_host, int(proxy_port))
    checks["loopback_works"] = _loopback_check()
    return checks


def runner_checks() -> dict[str, bool]:
    """From the RUNNER namespace: no *direct* egress, but the ACL gateway
    grants the pinned provider and refuses everything else."""
    checks = _no_egress_checks()
    gw_host, gw_port = GATEWAY.rsplit(":", 1)
    checks["gateway_reachable"] = _tcp_connect(gw_host, int(gw_port))
    checks["gateway_allows_pinned_provider"] = _gateway_connect(PROVIDER_HOST, 443) == 200
    blocked = _gateway_connect("example.com", 443)
    checks["gateway_blocks_other_hosts"] = blocked is not None and blocked != 200
    checks["loopback_works"] = _loopback_check()
    return checks


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--role", choices=("agent", "runner"), default="agent")
    args = parser.parse_args(argv)

    checks = agent_checks() if args.role == "agent" else runner_checks()
    print(json.dumps({"role": args.role, "checks": checks}, indent=2))
    ok = all(checks.values())
    print(f"EGRESS LOCKDOWN ({args.role}) " + ("VERIFIED" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
