"""Offline tests for the container-tier egress checker.

The kernel-level properties themselves can only be verified inside the
Linux container (see container/README.md); these tests pin the checker's
*logic* — CONNECT status parsing, allow/deny verdicts, loopback probe —
against a local fake gateway, so a regression in the script fails here
rather than on the pilot machine.
"""

from __future__ import annotations

import socket
import threading

import harness.runner.container.egress_check as egress_check


class _FakeGateway:
    """Answers HTTP CONNECT: 200 for the allowed host, 403 otherwise."""

    def __init__(self, allowed_host: str) -> None:
        self.allowed_host = allowed_host
        self._server = socket.socket()
        self._server.bind(("127.0.0.1", 0))
        self._server.listen(4)
        self.port = self._server.getsockname()[1]
        threading.Thread(target=self._serve, daemon=True).start()

    def _serve(self) -> None:
        while True:
            try:
                conn, _ = self._server.accept()
            except OSError:
                return
            with conn:
                head = conn.recv(1024).decode("latin-1", errors="replace")
                target = head.split()[1] if len(head.split()) > 1 else ""
                if target.startswith(self.allowed_host + ":"):
                    conn.sendall(b"HTTP/1.1 200 Connection established\r\n\r\n")
                else:
                    conn.sendall(b"HTTP/1.1 403 Filtered\r\n\r\n")

    def close(self) -> None:
        self._server.close()


def test_gateway_connect_parses_allow_and_deny(monkeypatch):
    gateway = _FakeGateway(allowed_host="api.openai.com")
    monkeypatch.setattr(egress_check, "GATEWAY", f"127.0.0.1:{gateway.port}")
    try:
        assert egress_check._gateway_connect("api.openai.com", 443) == 200
        assert egress_check._gateway_connect("example.com", 443) == 403
    finally:
        gateway.close()


def test_runner_checks_pass_with_conforming_gateway(monkeypatch):
    """Runner role: ACL gateway grants the provider, refuses other hosts."""
    gateway = _FakeGateway(allowed_host="api.openai.com")
    monkeypatch.setattr(egress_check, "GATEWAY", f"127.0.0.1:{gateway.port}")
    monkeypatch.setattr(egress_check, "PROVIDER_HOST", "api.openai.com")
    # Force the "outside" probes to unroutable addresses so they fail fast.
    monkeypatch.setattr(egress_check, "OUTSIDE_TCP_PROBES", (("192.0.2.1", 443),))
    monkeypatch.setattr(egress_check, "OUTSIDE_UDP_PROBES", (("192.0.2.2", 53),))
    monkeypatch.setattr(egress_check, "OUTSIDE_IPV6_PROBES", (("2001:db8::1", 443),))
    monkeypatch.setattr(egress_check, "TIMEOUT", 1.0)
    try:
        checks = egress_check.runner_checks()
        assert checks["gateway_reachable"] is True
        assert checks["gateway_allows_pinned_provider"] is True
        assert checks["gateway_blocks_other_hosts"] is True
        assert "no_docker_embedded_dns_egress" not in checks
        assert checks["docker_service_dns_allowed"] is True
    finally:
        gateway.close()


def test_runner_checks_allow_docker_service_dns(monkeypatch):
    """Runner service DNS is intentional; public UDP DNS remains blocked."""
    calls = []

    def fake_udp_dns(host, port=53):
        calls.append((host, port))
        if host == "127.0.0.11":
            return True
        return False

    monkeypatch.setattr(egress_check, "GATEWAY", "gateway:8888")
    monkeypatch.setattr(egress_check, "PROVIDER_HOST", "api.openai.com")
    monkeypatch.setattr(egress_check, "OUTSIDE_TCP_PROBES", (("192.0.2.1", 443),))
    monkeypatch.setattr(
        egress_check,
        "OUTSIDE_UDP_PROBES",
        (("8.8.8.8", 53), ("127.0.0.11", 53)),
    )
    monkeypatch.setattr(egress_check, "OUTSIDE_IPV6_PROBES", (("2001:db8::1", 443),))
    monkeypatch.setattr(
        egress_check,
        "_tcp_connect",
        lambda host, port, family=socket.AF_INET: host == "gateway",
    )
    monkeypatch.setattr(
        egress_check,
        "_gateway_connect",
        lambda host, port: 200 if host == "api.openai.com" else 403,
    )
    monkeypatch.setattr(egress_check, "_loopback_check", lambda: True)
    monkeypatch.setattr(egress_check, "_udp_dns_reachable", fake_udp_dns)
    monkeypatch.setattr(egress_check, "TIMEOUT", 1.0)
    checks = egress_check.runner_checks()
    assert checks["no_public_udp_dns_egress"] is True
    assert checks["docker_service_dns_allowed"] is True
    assert ("127.0.0.11", 53) not in calls


def _patch_agent_common(monkeypatch):
    monkeypatch.setattr(egress_check, "GATEWAY", "gateway:8888")
    monkeypatch.setattr(egress_check, "_http_healthcheck_ok", lambda base_url: True)
    monkeypatch.setattr(egress_check, "OUTSIDE_TCP_PROBES", (("192.0.2.1", 443),))
    monkeypatch.setattr(
        egress_check,
        "OUTSIDE_UDP_PROBES",
        (("8.8.8.8", 53), ("127.0.0.11", 53)),
    )
    monkeypatch.setattr(egress_check, "OUTSIDE_IPV6_PROBES", (("2001:db8::1", 443),))
    # Public UDP resolvers are unreachable on the agent's internal net.
    monkeypatch.setattr(egress_check, "_udp_dns_reachable", lambda host, port=53: False)
    monkeypatch.setattr(egress_check, "_tcp_connect", lambda *args, **kwargs: False)
    monkeypatch.setattr(egress_check, "_loopback_check", lambda: True)
    monkeypatch.setattr(egress_check, "TIMEOUT", 1.0)


def test_agent_checks_flag_docker_dns_when_external_name_resolves(monkeypatch):
    """Agent role: a resolved external name via 127.0.0.11 is a lockdown failure."""
    _patch_agent_common(monkeypatch)
    monkeypatch.setattr(
        egress_check,
        "_dns_external_name_resolves",
        lambda host, port=53: host == "127.0.0.11",
    )
    checks = egress_check.agent_checks(proxy_url="http://runner:8080")
    assert checks["no_public_udp_dns_egress"] is True
    assert checks["no_docker_embedded_dns_egress"] is False


def test_agent_checks_pass_docker_dns_when_forwarding_fails(monkeypatch):
    """A responding-but-non-resolving embedded resolver (dead upstream) passes.

    Docker always answers on 127.0.0.11; with a black-holed upstream the
    external lookup SERVFAILs, so nothing escapes and the check must pass.
    """
    _patch_agent_common(monkeypatch)
    monkeypatch.setattr(
        egress_check, "_dns_external_name_resolves", lambda host, port=53: False
    )
    checks = egress_check.agent_checks(proxy_url="http://runner:8080")
    assert checks["no_public_udp_dns_egress"] is True
    assert checks["no_docker_embedded_dns_egress"] is True
    assert all(checks.values())


def test_agent_checks_flag_reachable_gateway_as_failure(monkeypatch):
    """Agent role: a REACHABLE gateway is a lockdown failure (bypass path)."""
    gateway = _FakeGateway(allowed_host="api.openai.com")
    monkeypatch.setattr(egress_check, "GATEWAY", f"127.0.0.1:{gateway.port}")
    monkeypatch.setattr(egress_check, "_http_healthcheck_ok", lambda base_url: True)
    monkeypatch.setattr(egress_check, "OUTSIDE_TCP_PROBES", (("192.0.2.1", 443),))
    monkeypatch.setattr(egress_check, "OUTSIDE_UDP_PROBES", (("192.0.2.2", 53),))
    monkeypatch.setattr(egress_check, "OUTSIDE_IPV6_PROBES", (("2001:db8::1", 443),))
    monkeypatch.setattr(egress_check, "TIMEOUT", 1.0)
    try:
        checks = egress_check.agent_checks(proxy_url="http://runner:8080")
        # gateway is reachable here → the bypass guard must report failure...
        assert checks["gateway_unreachable_from_agent"] is False
        # ...while the proxy-reachable and loopback checks still pass.
        assert checks["recording_proxy_reachable"] is True
        assert checks["loopback_works"] is True
    finally:
        gateway.close()


class _FakeUDPResolver:
    """A minimal UDP DNS server that replies with a fixed 12-byte header.

    ``reply`` is the raw bytes to send back, or ``None`` to stay silent (so the
    probe times out). Lets us exercise ``_dns_external_name_resolves`` against a
    real socket without any Docker/embedded-DNS dependency.
    """

    def __init__(self, reply: bytes | None) -> None:
        self._reply = reply
        self._sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self._sock.bind(("127.0.0.1", 0))
        self.port = self._sock.getsockname()[1]
        threading.Thread(target=self._serve, daemon=True).start()

    def _serve(self) -> None:
        while True:
            try:
                _, addr = self._sock.recvfrom(512)
            except OSError:
                return
            if self._reply is not None:
                self._sock.sendto(self._reply, addr)

    def close(self) -> None:
        self._sock.close()


def _dns_header(id_bytes: bytes, flags: int, ancount: int) -> bytes:
    """A bare 12-byte DNS message header (qdcount=1, nscount=arcount=0)."""
    return (
        id_bytes
        + bytes([(flags >> 8) & 0xFF, flags & 0xFF])
        + b"\x00\x01"  # qdcount
        + bytes([(ancount >> 8) & 0xFF, ancount & 0xFF])
        + b"\x00\x00"  # nscount
        + b"\x00\x00"  # arcount
    )


def test_dns_external_name_resolves_true_only_on_successful_answer(monkeypatch):
    monkeypatch.setattr(egress_check, "TIMEOUT", 1.0)
    query_id = egress_check._DNS_QUERY[:2]
    # QR set, RCODE NOERROR (0), one answer record → the name resolved.
    resolver = _FakeUDPResolver(_dns_header(query_id, 0x8180, ancount=1))
    try:
        assert (
            egress_check._dns_external_name_resolves("127.0.0.1", resolver.port)
            is True
        )
    finally:
        resolver.close()


def test_dns_external_name_resolves_false_on_servfail_nodata_and_id_mismatch(
    monkeypatch,
):
    monkeypatch.setattr(egress_check, "TIMEOUT", 1.0)
    query_id = egress_check._DNS_QUERY[:2]
    cases = {
        # SERVFAIL (RCODE 2) — a black-holed upstream returns this; not resolved.
        "servfail": _dns_header(query_id, 0x8182, ancount=0),
        # NOERROR but zero answers (NODATA) — still not a resolution.
        "nodata": _dns_header(query_id, 0x8180, ancount=0),
        # A valid-looking answer but for a DIFFERENT query id — not our reply.
        "id_mismatch": _dns_header(b"\xff\xff", 0x8180, ancount=1),
    }
    for name, reply in cases.items():
        resolver = _FakeUDPResolver(reply)
        try:
            assert (
                egress_check._dns_external_name_resolves("127.0.0.1", resolver.port)
                is False
            ), name
        finally:
            resolver.close()


def test_dns_external_name_resolves_false_on_no_response(monkeypatch):
    monkeypatch.setattr(egress_check, "TIMEOUT", 0.5)
    resolver = _FakeUDPResolver(reply=None)  # silent → probe times out
    try:
        assert (
            egress_check._dns_external_name_resolves("127.0.0.1", resolver.port)
            is False
        )
    finally:
        resolver.close()


def test_gateway_connect_none_when_gateway_down(monkeypatch):
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        dead_port = probe.getsockname()[1]
    monkeypatch.setattr(egress_check, "GATEWAY", f"127.0.0.1:{dead_port}")
    assert egress_check._gateway_connect("api.openai.com", 443) is None


def test_tcp_connect_true_on_listener_false_on_closed_port():
    listener = socket.socket()
    listener.bind(("127.0.0.1", 0))
    listener.listen(1)
    port = listener.getsockname()[1]
    try:
        assert egress_check._tcp_connect("127.0.0.1", port) is True
    finally:
        listener.close()
    assert egress_check._tcp_connect("127.0.0.1", port) is False


def test_load_proxy_url_prefers_endpoint_json(tmp_path):
    path = tmp_path / "proxy.json"
    path.write_text('{"base_url": "http://runner:43123"}\n', encoding="utf-8")
    assert egress_check._load_proxy_url(str(path), None) == "http://runner:43123"


def test_documented_runner_commands_use_compose_aliases():
    root = egress_check.Path(__file__).resolve().parents[1] / "container"
    readme = root.joinpath("README.md").read_text(encoding="utf-8")
    compose = root.joinpath("docker-compose.yml").read_text(encoding="utf-8")
    assert "docker compose run --rm --use-aliases runner" in readme
    assert "docker compose run --rm --use-aliases runner" in compose
    assert "egress_check --role agent" in readme
    agent_block = compose.split("  agent:", 1)[1]
    assert "depends_on:\n      - runner" not in agent_block
    assert "dns:\n      - 127.0.0.1" in agent_block
